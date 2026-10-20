#include <algorithm>
#include <cctype>
#include <cstdint>
#include <limits>
#include <filesystem>
#include <iterator>
#include <map>
#include <memory>
#include <optional>
#include <set>
#include <string>
#include <system_error>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

#include "clang/AST/ASTConsumer.h"
#include "clang/AST/ASTContext.h"
#include "clang/AST/Attr.h"
#include "clang/AST/Decl.h"
#include "clang/AST/DeclCXX.h"
#include "clang/AST/DeclTemplate.h"
#include "clang/AST/Expr.h"
#include "clang/AST/ExprCXX.h"
#include "clang/AST/RecordLayout.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/AST/Stmt.h"
#include "clang/AST/StmtCXX.h"
#include "clang/AST/TypeLoc.h"
#include "clang/Basic/LangStandard.h"
#include "clang/Basic/Builtins.h"
#include "clang/Basic/DiagnosticSema.h"
#include "clang/Basic/SourceManager.h"
#include "clang/Basic/Version.h"
#include "clang/Frontend/CompilerInstance.h"
#include "clang/Frontend/FrontendAction.h"
#include "clang/Index/USRGeneration.h"
#include "clang/Lex/Lexer.h"
#include "clang/Lex/PPCallbacks.h"
#include "clang/Lex/Preprocessor.h"
#include "clang/Sema/Sema.h"
#include "clang/Tooling/ArgumentsAdjusters.h"
#include "clang/Tooling/CompilationDatabase.h"
#include "clang/Tooling/JSONCompilationDatabase.h"
#include "clang/Tooling/Tooling.h"
#include "llvm/ADT/SmallString.h"
#include "llvm/Support/JSON.h"
#include "llvm/Support/SaveAndRestore.h"
#include "llvm/Support/raw_ostream.h"

namespace {
// Resource policy; the independent artifact checker enforces the same bounds.
constexpr std::size_t kMaxRecordDeclarations = 256;
constexpr std::size_t kMaxConstantDeclarations = 1024;
constexpr std::size_t kMaxFunctionDeclarations = 1024;
constexpr unsigned kMaxLocalDeclarations = 1024;
constexpr unsigned kMaxCleanupScopes = 256;
constexpr std::size_t kMaxScalarConversions = 256;

constexpr const char *kClangVersion = "19.1.7";
#ifndef CLICK_CLANG_RESOURCE_DIR
#error "build with scripts/build-cpp-exporter.sh, which defines CLICK_CLANG_RESOURCE_DIR"
#endif
// The pinned Clang's resource directory, recorded when the exporter is built.
constexpr const char *kClangResourceDir = CLICK_CLANG_RESOURCE_DIR;
constexpr std::size_t kMaxPreprocessorFiles = 4096;

struct GenericTemplate {
  std::string qualified_name;
  std::vector<std::string> parameters;
};

// The abstract type a generic class template's parameter named `name` is
// instantiated at: a trivially copyable record of one machine word, which a
// body can only copy, declared ahead of the translation unit.
std::string archetype_record_name(const std::string &name) {
  return "__click_" + name;
}

// `Stack<T>` or `ns::Pair<K, V>`: a class template's qualified name and its
// type parameters' names, each an identifier.
std::optional<GenericTemplate> parse_generic_template(const std::string &text) {
  const auto open = text.find('<');
  if (open == std::string::npos || open == 0 || text.back() != '>')
    return std::nullopt;
  GenericTemplate result;
  result.qualified_name = text.substr(0, open);
  std::string parameter;
  auto is_identifier = [](const std::string &word) {
    return !word.empty() && !std::isdigit(static_cast<unsigned char>(word.front())) &&
           std::all_of(word.begin(), word.end(), [](char character) {
             return std::isalnum(static_cast<unsigned char>(character)) || character == '_';
           }) &&
           word.rfind("__", 0) != 0;
  };
  for (std::size_t at = open + 1; at < text.size(); ++at) {
    const char character = text[at];
    if (character == ',' || at + 1 == text.size()) {
      if (!is_identifier(parameter) ||
          std::find(result.parameters.begin(), result.parameters.end(), parameter) !=
              result.parameters.end())
        return std::nullopt;
      result.parameters.push_back(parameter);
      parameter.clear();
    } else if (character != ' ') {
      parameter.push_back(character);
    }
  }
  for (std::size_t at = 0; at < result.qualified_name.size(); ++at) {
    const char character = result.qualified_name[at];
    if (!std::isalnum(static_cast<unsigned char>(character)) && character != '_' &&
        character != ':')
      return std::nullopt;
  }
  return result;
}

struct Options {
  std::string logical_source;
  std::string logical_source_path;
  std::vector<std::string> functions;
  std::string source;
  std::string dependency_root;
  std::string compilation_database;
  std::string exception_behavior = "normal_only";
  std::map<std::string, llvm::json::Value> library_assertions;
  std::string compilation_directory;
  std::string compilation_file;
  std::vector<std::string> compilation_command;
  // The class templates verified once for every type argument, each with
  // its type parameters' names as the sidecar writes them: `Stack<T>`.
  std::vector<GenericTemplate> generic_templates;
};

struct ExportState {
  std::optional<llvm::json::Value> artifact;
  std::string error;
  std::map<std::string, std::string> preprocessor_files;
};

std::optional<Options> parse_options(int argc, const char **argv) {
  Options result;
  for (int index = 1; index < argc; index += 2) {
    if (index + 1 >= argc) {
      llvm::errs() << "error: every exporter option requires a value\n";
      return std::nullopt;
    }
    const std::string option = argv[index];
    const std::string value = argv[index + 1];
    if (option == "--logical-source") {
      result.logical_source = value;
    } else if (option == "--logical-source-path") {
      result.logical_source_path = value;
    } else if (option == "--function") {
      if (value.empty() || result.functions.size() >= 64 ||
          std::find(result.functions.begin(), result.functions.end(), value) !=
              result.functions.end()) {
        llvm::errs() << "error: --function names must be unique and at most 64\n";
        return std::nullopt;
      }
      result.functions.push_back(value);
    } else if (option == "--generic-template") {
      auto parsed = parse_generic_template(value);
      if (!parsed || result.generic_templates.size() >= 16 ||
          std::any_of(result.generic_templates.begin(), result.generic_templates.end(),
                      [&](const GenericTemplate &other) {
                        return other.qualified_name == parsed->qualified_name;
                      })) {
        llvm::errs() << "error: --generic-template names a class template and its "
                        "type parameters, `Stack<T>`, each at most once and at most 16\n";
        return std::nullopt;
      }
      result.generic_templates.push_back(std::move(*parsed));
    } else if (option == "--source") {
      result.source = value;
    } else if (option == "--dependency-root") {
      result.dependency_root = value;
    } else if (option == "--compilation-database") {
      result.compilation_database = value;
    } else if (option == "--library-assertions") {
      auto parsed = llvm::json::parse(value);
      if (!parsed || !parsed->getAsArray() || parsed->getAsArray()->size() > 64) {
        llvm::errs() << "error: invalid library assertion inventory\n";
        if (!parsed) llvm::consumeError(parsed.takeError());
        return std::nullopt;
      }
      for (auto &entry : *parsed->getAsArray()) {
        const auto *object = entry.getAsObject();
        if (!object || !object->getString("function") ||
            !object->getString("header") || !object->getString("sha256") ||
            (object->getString("kind") != "checked_boolean_statement" &&
             object->getString("kind") != "checked_boolean_statement_with_consteval_metadata" &&
             object->getString("kind") != "checked_boolean_statement_with_literal_metadata") ||
            !result.library_assertions.emplace(object->getString("function")->str(), std::move(entry)).second) {
          llvm::errs() << "error: invalid or duplicate library assertion contract\n";
          return std::nullopt;
        }
      }
    } else if (option == "--exception-behavior") {
      if (value != "normal_only" && value != "scalar_int32") {
        llvm::errs() << "error: unsupported exception behavior `" << value << "`\n";
        return std::nullopt;
      }
      result.exception_behavior = value;
    } else {
      llvm::errs() << "error: unknown exporter option `" << option << "`\n";
      return std::nullopt;
    }
  }
  if (result.logical_source.empty() || result.logical_source_path.empty() ||
      result.functions.empty() || result.source.empty() ||
      result.dependency_root.empty() ||
      result.compilation_database.empty()) {
    llvm::errs()
        << "error: --logical-source, --logical-source-path, --function, "
           "--source, --dependency-root, and --compilation-database are required\n";
    return std::nullopt;
  }
  return result;
}

bool has_untracked_preprocessor_input(const std::string &argument) {
  // Textual includes are inventoried by PreprocessorFiles. These modes can
  // supply AST or file contents without a corresponding lexed-file callback.
  return (!argument.empty() && argument.front() == '@') ||
         argument == "-Xclang" || argument == "-Xpreprocessor" ||
         argument.rfind("-include-pch", 0) == 0 ||
         argument.rfind("-include-pth", 0) == 0 ||
         argument.rfind("-ivfsoverlay", 0) == 0 ||
         argument.rfind("-fmodules", 0) == 0 ||
         argument.rfind("-fcxx-modules", 0) == 0 ||
         argument.rfind("-fmodule-", 0) == 0 ||
         argument.rfind("-fprebuilt-module-path", 0) == 0 ||
         argument.rfind("-fplugin", 0) == 0;
}

class SemanticExporter : public clang::RecursiveASTVisitor<SemanticExporter> {
public:
  SemanticExporter(clang::CompilerInstance &compiler, std::string logical_source,
                   std::string logical_source_path,
                   std::vector<std::string> selected_names,
                   std::string dependency_root,
                   std::string compilation_directory,
                   std::string compilation_file,
                   std::vector<std::string> compilation_command,
                   std::string exception_behavior,
                   const std::map<std::string, llvm::json::Value> &library_assertions,
                   std::vector<GenericTemplate> generic_templates,
                   ExportState &state)
      : compiler_(compiler), context_(compiler.getASTContext()),
        source_manager_(context_.getSourceManager()),
        logical_source_(std::move(logical_source)),
        logical_source_path_(std::move(logical_source_path)),
        selected_names_(std::move(selected_names)),
        dependency_root_(std::move(dependency_root)),
        compilation_directory_(std::move(compilation_directory)),
        compilation_file_(std::move(compilation_file)),
        compilation_command_(std::move(compilation_command)),
        exception_behavior_(std::move(exception_behavior)),
        library_assertions_(library_assertions),
        generic_templates_(std::move(generic_templates)), state_(state) {}

  bool VisitClassTemplateDecl(clang::ClassTemplateDecl *declaration) {
    class_templates_.emplace(declaration->getQualifiedNameAsString(),
                             declaration->getCanonicalDecl());
    return true;
  }

  bool VisitCXXRecordDecl(clang::CXXRecordDecl *record) {
    if (record->getDeclContext()->isTranslationUnit() &&
        record->isThisDeclarationADefinition() &&
        source_manager_.isWrittenInBuiltinFile(record->getLocation())) {
      for (const GenericTemplate &generic : generic_templates_)
        for (const std::string &name : generic.parameters)
          if (record->getName() == archetype_record_name(name))
            archetypes_.emplace(name, record);
    }
    return true;
  }

  bool VisitFunctionDecl(clang::FunctionDecl *declaration) {
    // Every virtual method the translation unit declares outside system
    // headers, so a reachable one brings the methods that override it,
    // which a call through it may reach.
    if (const auto *method = llvm::dyn_cast<clang::CXXMethodDecl>(declaration);
        method != nullptr && method->isVirtual() &&
        method == method->getCanonicalDecl() &&
        !source_manager_.isInSystemHeader(
            source_manager_.getExpansionLoc(method->getLocation())))
      virtual_methods_.push_back(method);
    if (declaration->isThisDeclarationADefinition() &&
        is_in_logical_source(declaration->getLocation())) {
      const std::string name = declaration->getQualifiedNameAsString();
      if (std::find(selected_names_.begin(), selected_names_.end(), name) !=
          selected_names_.end()) {
        matches_[name].push_back(declaration);
      }
    }
    return true;
  }

  void finish() {
    if (exception_behavior_ == "scalar_int32" &&
        !context_.getLangOpts().CXXExceptions) {
      fail({}, "scalar int32 exception profile requires C++ exceptions enabled");
      return;
    }
    if (!resolve_generic_templates())
      return;
    // Each virtual method's overrides, indexed once.
    for (const clang::CXXMethodDecl *method : virtual_methods_)
      for (const clang::CXXMethodDecl *overridden : method->overridden_methods())
        overriders_[overridden->getCanonicalDecl()].push_back(method);
    // Every selected function is known before any is lowered, so a selected
    // function that another one calls is exported once, as selected.
    std::vector<const clang::FunctionDecl *> selected;
    for (const std::string &name : selected_names_) {
      const auto found = matches_.find(name);
      if (found == matches_.end()) {
        fail({}, "selected function `" + name + "` was not found");
        return;
      }
      if (found->second.size() != 1) {
        fail(found->second.front()->getLocation(),
             "selected function `" + name + "` is overloaded");
        return;
      }
      const clang::FunctionDecl *definition = found->second.front()->getDefinition();
      if (definition == nullptr) {
        fail(found->second.front()->getLocation(),
             "selected function has no reachable definition");
        return;
      }
      known_functions_.insert(definition->getCanonicalDecl());
      selected.push_back(definition);
    }
    llvm::json::Array functions;
    for (const clang::FunctionDecl *definition : selected) {
      auto function = lower_function(definition);
      if (!function) {
        return;
      }
      functions.push_back(std::move(*function));
    }
    llvm::json::Array reachable_functions;
    for (std::size_t index = 0; index < reachable_definitions_.size(); ++index) {
      auto reachable = lower_function(reachable_definitions_[index]);
      if (!reachable) {
        return;
      }
      reachable_functions.push_back(std::move(*reachable));
    }
    for (std::size_t index = 0; index < constant_definitions_.size(); ++index) {
      if (!discover_constant_dependencies(
              constant_definitions_[index]->getInit())) {
        return;
      }
    }
    std::stable_sort(
        constant_definitions_.begin(), constant_definitions_.end(),
        [this](const clang::VarDecl *left, const clang::VarDecl *right) {
          return source_manager_.isBeforeInTranslationUnit(
              source_manager_.getExpansionLoc(left->getLocation()),
              source_manager_.getExpansionLoc(right->getLocation()));
        });
    llvm::json::Array constants;
    for (const clang::VarDecl *constant : constant_definitions_) {
      auto lowered = lower_constant(constant, selected.front());
      if (!lowered) {
        return;
      }
      constants.push_back(std::move(*lowered));
    }
    if (!check_generic_records())
      return;
    llvm::json::Array records;
    for (const clang::CXXRecordDecl *record : record_definitions_) {
      auto lowered = lower_record(record);
      if (!lowered) {
        return;
      }
      records.push_back(std::move(*lowered));
    }

    llvm::json::Object profile;
    profile["frontend"] = "clang";
    profile["frontend_version"] = clang::getClangFullVersion();
    profile["standard"] = clang::LangStandard::getLangStandardForKind(
                              context_.getLangOpts().LangStd)
                              .getName();
    profile["target"] = context_.getTargetInfo().getTriple().str();
    profile["exceptions"] =
        static_cast<bool>(context_.getLangOpts().CXXExceptions);
    profile["rtti"] = static_cast<bool>(context_.getLangOpts().RTTI);
    profile["compilation_directory"] = compilation_directory_;
    profile["compilation_file"] = compilation_file_;
    llvm::json::Array compilation_command;
    for (const std::string &argument : compilation_command_) {
      compilation_command.push_back(argument);
    }
    profile["compilation_command"] = std::move(compilation_command);

    llvm::json::Object artifact;
    artifact["schema"] = 60;
    artifact["language"] = "c++";
    artifact["profile"] = std::move(profile);
    artifact["exception_behavior"] = exception_behavior_;
    artifact["logical_source"] = logical_source_;
    llvm::json::Array dependencies;
    for (const std::string &dependency : dependency_sources_) {
      dependencies.push_back(dependency);
    }
    artifact["dependencies"] = std::move(dependencies);
    llvm::json::Array preprocessor_files;
    for (const auto &[accessed_path, canonical_path] :
         state_.preprocessor_files) {
      llvm::json::Object file;
      file["accessed_path"] = accessed_path;
      file["canonical_path"] = canonical_path;
      preprocessor_files.push_back(std::move(file));
    }
    artifact["preprocessor_files"] = std::move(preprocessor_files);
    artifact["constants"] = std::move(constants);
    artifact["records"] = std::move(records);
    artifact["functions"] = std::move(functions);
    artifact["reachable_functions"] = std::move(reachable_functions);
    state_.artifact.emplace(std::move(artifact));
  }

private:
  enum class CleanupScopeKind { None, Conditional, Try };

  using Json = llvm::json::Value;

  std::vector<const clang::CXXMethodDecl *> virtual_methods_;
  std::map<const clang::CXXMethodDecl *, std::vector<const clang::CXXMethodDecl *>>
      overriders_;

  struct LoweredCall {
    llvm::json::Object callee;
    llvm::json::Array arguments;
    Json span;
  };

  struct LoweredMember {
    Json object;
    Json field;
  };

  // These statements have no runtime operation. A concrete successful
  // static_assert was checked by pinned Clang; never erase a dependent or
  // failed assertion. Its source remains covered by the import closure.
  static bool is_checked_runtime_noop(const clang::Stmt *statement) {
    if (llvm::isa_and_nonnull<clang::NullStmt>(statement)) return true;
    const auto *declaration = llvm::dyn_cast_or_null<clang::DeclStmt>(statement);
    const auto *assertion = declaration != nullptr && declaration->isSingleDecl()
        ? llvm::dyn_cast<clang::StaticAssertDecl>(declaration->getSingleDecl())
        : nullptr;
    return assertion != nullptr && !assertion->isFailed() &&
           !assertion->getAssertExpr()->isValueDependent() &&
           !assertion->getAssertExpr()->isTypeDependent();
  }

  std::optional<Json> lower_function(const clang::FunctionDecl *declaration) {
    if (is_axiom(declaration))
      return lower_axiom(declaration);
    if (!refuse_optimizer_promises(declaration))
      return std::nullopt;
    auto source = executable_source(declaration->getLocation());
    if (!source) {
      fail(declaration->getLocation(), "reachable C++ definitions require a selected or dependency source");
      return std::nullopt;
    }
    llvm::SaveAndRestore<std::string> body_source(function_source_, *source);
    if (*source != logical_source_)
      dependency_sources_.insert(*source);
    if (declaration->isDependentContext() ||
        declaration->getType()->isDependentType()) {
      fail(declaration->getLocation(),
           "select an ordinary C++ caller of concrete template instances, not "
           "a dependent template pattern");
      return std::nullopt;
    }
    // A generic class template's method at other type arguments is its
    // method at abstract ones, verified once: only its signature is
    // exported, with the method it is an instance of.
    const clang::FunctionDecl *generic = generic_counterpart(declaration);
    if (!state_.error.empty() || (generic != nullptr && !remember_function(generic)))
      return std::nullopt;
    if (is_generic_body(declaration) && !check_generic_pattern(declaration))
      return std::nullopt;
    const auto *constructor =
        llvm::dyn_cast<clang::CXXConstructorDecl>(declaration);
    const auto *destructor =
        llvm::dyn_cast<clang::CXXDestructorDecl>(declaration);
    // A lambda's call operator is exported as a free function of its
    // parameters; the lambdas admitted capture nothing, so it reads no state.
    const auto *lambda_call = llvm::dyn_cast<clang::CXXMethodDecl>(declaration);
    if (lambda_call != nullptr && !lambda_call->getParent()->isLambda())
      lambda_call = nullptr;
    std::optional<std::string> lambda_function_name;
    if (lambda_call != nullptr) {
      lambda_function_name = lambda_name(lambda_call);
      if (!lambda_function_name)
        return std::nullopt;
    }
    const auto *method = lambda_call != nullptr
                             ? nullptr
                             : llvm::dyn_cast<clang::CXXMethodDecl>(declaration);
    const bool ordinary_method =
        method != nullptr && constructor == nullptr && destructor == nullptr;
    if (ordinary_method && (method->isVolatile() ||
                            method->getRefQualifier() != clang::RQ_None ||
                            method->isDeleted() || method->isVariadic())) {
      fail(method->getLocation(),
           "supported C++ methods must be non-volatile, non-deleted, unqualified, "
           "and non-variadic");
      return std::nullopt;
    }
    std::optional<Json> virtual_method;
    if (ordinary_method && method->isVirtual()) {
      virtual_method = lower_virtual_method(method);
      if (!virtual_method)
        return std::nullopt;
    }
    const bool pure_virtual = ordinary_method && method->isPureVirtual();
    if (constructor != nullptr &&
        !validate_constructor(constructor,
                              constructor->getParent()->getDefinition())) {
      return std::nullopt;
    }
    const auto *prototype =
        declaration->getType()->getAs<clang::FunctionProtoType>();
    if (prototype == nullptr) {
      fail(declaration->getLocation(),
           "the supported C++ function must have a prototype");
      return std::nullopt;
    }
    if (exception_behavior_ == "scalar_int32" && prototype->isNothrow() &&
        constructor == nullptr && destructor == nullptr) {
      fail(declaration->getLocation(),
           "scalar int32 exception profile does not model noexcept termination");
      return std::nullopt;
    }
    if (!prototype->isNothrow() &&
        (!context_.getLangOpts().CXXExceptions || constructor != nullptr ||
         destructor != nullptr)) {
      fail(declaration->getLocation(),
           "the supported C++ function must declare noexcept outside the "
           "exception-enabled object-free profile");
      return std::nullopt;
    }
    std::optional<Json> return_type;
    llvm::json::Object function_kind;
    if (constructor != nullptr || destructor != nullptr) {
      const auto *method = llvm::cast<clang::CXXMethodDecl>(declaration);
      const auto *record = method->getParent()->getDefinition();
      if (record == nullptr || !remember_record(record)) {
        return std::nullopt;
      }
      llvm::json::Object void_type;
      void_type["kind"] = "void";
      return_type.emplace(std::move(void_type));
      function_kind["kind"] =
          constructor != nullptr ? "constructor" : "destructor";
      function_kind["record_declaration_id"] = declaration_id(record);
      function_kind["record_name"] = record_name(record);
    } else {
      return_type =
          lower_type(declaration->getReturnType(),
                     declaration->getReturnTypeSourceRange().getBegin(),
                     direct_source_alias(declaration->getTypeSourceInfo()));
      if (!return_type) {
        return std::nullopt;
      }
      function_kind["kind"] =
          ordinary_method ? (method->isStatic() ? "static_method" : "method")
                          : "free";
      if (ordinary_method) {
        const auto *record = method->getParent()->getDefinition();
        if (record == nullptr ||
            (!method->isStatic() && !remember_record(record)))
          return std::nullopt;
        function_kind["record_declaration_id"] = declaration_id(record);
        function_kind["record_name"] = record_name(record);
        if (!method->isStatic())
          function_kind["is_const"] = method->isConst();
      }
    }
    llvm::json::Array parameters;
    // A lambda's captures are its leading parameters, named for the captured
    // variables, so its body's reads of them read the parameters.
    std::size_t closure_captures = 0;
    if (lambda_call != nullptr) {
      auto captures = lambda_captures(lambda_call->getParent(), lambda_call->getLocation());
      if (!captures)
        return std::nullopt;
      for (const clang::VarDecl *variable : *captures) {
        auto value_type =
            lower_type(variable->getType().getUnqualifiedType(), variable->getLocation());
        if (!value_type)
          return std::nullopt;
        llvm::json::Object capture;
        capture["declaration_id"] = declaration_id(variable);
        capture["name"] = variable->getNameAsString();
        capture["value_type"] = std::move(*value_type);
        capture["span"] = span(variable->getSourceRange());
        parameters.push_back(std::move(capture));
      }
      closure_captures = captures->size();
    }
    if (method != nullptr && !method->isStatic()) {
      const auto *method = llvm::cast<clang::CXXMethodDecl>(declaration);
      const auto *record = method->getParent()->getDefinition();
      llvm::json::Object record_type;
      record_type["kind"] = "record";
      record_type["declaration_id"] = declaration_id(record);
      record_type["name"] = record_name(record);
      record_type["is_const"] = method->isConst();
      llvm::json::Object reference_type;
      reference_type["kind"] = "lvalue_reference";
      reference_type["pointee"] = std::move(record_type);
      llvm::json::Object self;
      self["declaration_id"] = object_self_id(method);
      self["name"] = "self";
      self["value_type"] = std::move(reference_type);
      self["span"] = span(method->getNameInfo().getSourceRange());
      parameters.push_back(std::move(self));
    }
    for (const clang::ParmVarDecl *parameter : declaration->parameters()) {
      if (ordinary_method && method->isStatic() &&
          (!parameter->getType()->isIntegerType() ||
           parameter->getType().hasQualifiers())) {
        fail(parameter->getLocation(),
             "static C++ helpers require by-value scalar parameters");
        return std::nullopt;
      }
      auto lowered = lower_parameter(parameter);
      if (!lowered) {
        return std::nullopt;
      }
      parameters.push_back(std::move(*lowered));
    }
    const auto *body =
        llvm::dyn_cast_or_null<clang::CompoundStmt>(declaration->getBody());
    if (pure_virtual || generic != nullptr) {
      // A pure virtual method is only its interface: the sidecar's contract
      // for it is what a call through it assumes. So is a generic method's
      // instance.
      body = nullptr;
    } else if (body == nullptr ||
               (body->body_empty() && constructor == nullptr &&
                !(llvm::isa<clang::CXXDestructorDecl>(declaration) &&
                  effectful_base_destructor(
                      llvm::cast<clang::CXXDestructorDecl>(declaration)
                          ->getParent()
                          ->getDefinition()) != nullptr))) {
      fail(declaration->getLocation(),
           "the supported C++ function requires a nonempty compound body");
      return std::nullopt;
    }

    llvm::json::Array statements;
    if (constructor != nullptr && generic != nullptr) {
      fail(constructor->getLocation(),
           "a generic class template's written constructor is outside the supported slice");
      return std::nullopt;
    }
    if (constructor != nullptr) {
      const auto *record = constructor->getParent()->getDefinition();
      if (has_stateless_field(record)) {
        fail(constructor->getLocation(),
             "supported constructors require records without stateless members");
        return std::nullopt;
      }
      // A base built by its own constructor: that call, on the base
      // subobject, before the members.
      for (const clang::CXXCtorInitializer *initializer : constructor->inits()) {
        if (!initializer->isBaseInitializer() || !initializer->isWritten())
          continue;
        const auto *construction = llvm::dyn_cast<clang::CXXConstructExpr>(
            initializer->getInit()->IgnoreParenImpCasts());
        const auto *selected =
            construction == nullptr ? nullptr : construction->getConstructor();
        const auto *definition =
            selected == nullptr
                ? nullptr
                : llvm::dyn_cast_or_null<clang::CXXConstructorDecl>(
                      selected->getDefinition());
        const auto *base_record =
            initializer->getBaseClass()->getAsCXXRecordDecl()->getDefinition();
        if (definition == nullptr ||
            construction->getNumArgs() != definition->getNumParams()) {
          fail(initializer->getSourceLocation(),
               "C++ base construction requires a resolved direct constructor call");
          return std::nullopt;
        }
        llvm::json::Array arguments;
        for (unsigned index = 0; index < construction->getNumArgs(); ++index) {
          auto argument = lower_call_argument(construction->getArg(index),
                                              definition->getParamDecl(index),
                                              constructor);
          if (!argument) return std::nullopt;
          arguments.push_back(std::move(*argument));
        }
        if (!remember_function(definition)) return std::nullopt;
        llvm::json::Object object;
        object["declaration_id"] = object_self_id(constructor);
        object["name"] = "self";
        object["span"] = span(constructor->getNameInfo().getSourceRange());
        llvm::json::Object base_reference;
        base_reference["record_declaration_id"] = declaration_id(record);
        base_reference["base_declaration_id"] = declaration_id(base_record);
        base_reference["base_name"] = record_name(base_record);
        base_reference["span"] = span(initializer->getSourceRange());
        llvm::json::Object reference;
        reference["declaration_id"] = declaration_id(definition);
        reference["name"] = constructor_name(definition);
        reference["span"] = span(initializer->getSourceRange());
        llvm::json::Object statement;
        statement["kind"] = "base_construct";
        statement["object"] = std::move(object);
        statement["base"] = std::move(base_reference);
        statement["callee"] = std::move(reference);
        statement["arguments"] = std::move(arguments);
        statement["span"] = span(initializer->getSourceRange());
        statements.push_back(std::move(statement));
      }
      for (const clang::FieldDecl *field : record->fields()) {
        const clang::CXXCtorInitializer *initializer = nullptr;
        for (const clang::CXXCtorInitializer *candidate : constructor->inits()) {
          if (candidate->isMemberInitializer() &&
              candidate->getMember() == field) {
            initializer = candidate;
            break;
          }
        }
        if (initializer == nullptr) {
          fail(constructor->getLocation(),
               "supported constructor is missing a validated member initializer");
          return std::nullopt;
        }
        llvm::json::Object object;
        object["declaration_id"] = object_self_id(constructor);
        object["name"] = "self";
        object["span"] = span(constructor->getNameInfo().getSourceRange());
        llvm::json::Object field_reference;
        field_reference["record_declaration_id"] = declaration_id(record);
        field_reference["declaration_id"] = declaration_id(field);
        field_reference["name"] = field->getNameAsString();
        field_reference["span"] = span(field->getSourceRange());
        llvm::json::Object statement;
        statement["object"] = std::move(object);
        statement["field"] = std::move(field_reference);
        if (field->getType()->isRecordType() && archetype_name(field->getType()) == nullptr) {
          const auto *construction = llvm::dyn_cast<clang::CXXConstructExpr>(initializer->getInit()->IgnoreParenImpCasts());
          const auto *selected = construction == nullptr ? nullptr : construction->getConstructor();
          const auto *definition = selected == nullptr ? nullptr : llvm::dyn_cast_or_null<clang::CXXConstructorDecl>(selected->getDefinition());
          if (construction == nullptr || definition == nullptr ||
              construction->getConstructionKind() != clang::CXXConstructionKind::Complete ||
              definition->getParent()->getCanonicalDecl() != field->getType()->getAsCXXRecordDecl()->getCanonicalDecl() ||
              construction->getNumArgs() != definition->getNumParams()) {
            fail(initializer->getSourceLocation(), "embedded C++ field initialization requires a resolved direct constructor call");
            return std::nullopt;
          }
          llvm::json::Array arguments;
          for (unsigned index = 0; index < construction->getNumArgs(); ++index) {
            auto argument = lower_call_argument(construction->getArg(index), definition->getParamDecl(index), constructor);
            if (!argument) return std::nullopt;
            arguments.push_back(std::move(*argument));
          }
          if (!remember_function(definition)) return std::nullopt;
          llvm::json::Object reference;
          reference["declaration_id"] = declaration_id(definition);
          reference["name"] = constructor_name(definition);
          reference["span"] = span(initializer->getSourceRange());
          statement["kind"] = "member_construct";
          statement["callee"] = std::move(reference);
          statement["arguments"] = std::move(arguments);
        } else {
          auto value = lower_expression(initializer->getInit(), constructor);
          if (!value) return std::nullopt;
          statement["kind"] = "member_store";
          statement["value"] = std::move(*value);
        }
        statement["span"] = span(initializer->getSourceRange());
        statements.push_back(std::move(statement));
      }
    }
    for (const clang::Stmt *statement :
         body == nullptr ? llvm::ArrayRef<clang::Stmt *>() : body->body()) {
      if (is_checked_runtime_noop(statement)) continue;
      auto lowered = lower_statement(statement, declaration, true, true);
      if (!lowered) {
        return std::nullopt;
      }
      statements.push_back(std::move(*lowered));
    }
    // A derived destructor then destroys its base: the base's written
    // destructor on the base subobject.
    if (const auto *destructor =
            llvm::dyn_cast<clang::CXXDestructorDecl>(declaration)) {
      const auto *record = destructor->getParent()->getDefinition();
      if (const auto *base_destructor = effectful_base_destructor(record)) {
        const auto *definition = llvm::dyn_cast_or_null<clang::CXXDestructorDecl>(
            base_destructor->getDefinition());
        const auto *base_record = base_destructor->getParent()->getDefinition();
        if (definition == nullptr || !remember_function(definition))
          return std::nullopt;
        llvm::json::Object object;
        object["declaration_id"] = object_self_id(destructor);
        object["name"] = "self";
        object["span"] = span(destructor->getNameInfo().getSourceRange());
        llvm::json::Object base_reference;
        base_reference["record_declaration_id"] = declaration_id(record);
        base_reference["base_declaration_id"] = declaration_id(base_record);
        base_reference["base_name"] = record_name(base_record);
        base_reference["span"] = span(record->bases_begin()->getSourceRange());
        llvm::json::Object reference;
        reference["declaration_id"] = declaration_id(definition);
        reference["name"] = destructor_name(definition);
        reference["span"] = span(definition->getNameInfo().getSourceRange());
        llvm::json::Object statement;
        statement["kind"] = "base_destruct";
        statement["object"] = std::move(object);
        statement["base"] = std::move(base_reference);
        statement["callee"] = std::move(reference);
        statement["span"] = span(destructor->getSourceRange());
        statements.push_back(std::move(statement));
      }
    }

    llvm::json::Object result;
    result["declaration_id"] = declaration_id(declaration);
    result["name"] = lambda_function_name ? *lambda_function_name
                     : ordinary_method       ? method_name(method)
                     : constructor == nullptr
                         ? (destructor == nullptr ? function_name(declaration)
                                                  : destructor_name(destructor))
                         : constructor_name(constructor);
    result["path"] = function_path(declaration);
    result["function_kind"] = std::move(function_kind);
    result["return_type"] = std::move(*return_type);
    result["parameters"] = std::move(parameters);
    result["declared_noexcept"] = prototype->isNothrow();
    if (closure_captures != 0)
      result["closure_captures"] = static_cast<int64_t>(closure_captures);
    result["span"] = span(declaration->getSourceRange());
    result["body"] = std::move(statements);
    if (virtual_method)
      result["virtual"] = std::move(*virtual_method);
    if (generic != nullptr) {
      llvm::json::Object reference;
      reference["declaration_id"] = declaration_id(generic);
      reference["name"] = method_name(llvm::cast<clang::CXXMethodDecl>(generic));
      reference["span"] = span(generic->getSourceRange());
      result["generic_instance"] = std::move(reference);
    }
    if (!state_.error.empty()) {
      return std::nullopt;
    }
    return Json(std::move(result));
  }

  // A virtual method's dispatch: whether it is pure, the methods it
  // overrides, whose contracts it must refine, and, remembered here, every
  // method of the source that overrides it, which a call through it may
  // reach. A method declared outside the source is not seen, and so not
  // checked: an override in another translation unit is trusted to keep the
  // interface, as any unverified code is.
  std::optional<Json> lower_virtual_method(const clang::CXXMethodDecl *method) {
    if (method->isPureVirtual() && method->isDefined()) {
      fail(method->getLocation(),
           "a pure virtual C++ method with a definition remains unsupported");
      return std::nullopt;
    }
    const auto same_signature = [this](const clang::CXXMethodDecl *left,
                                       const clang::CXXMethodDecl *right) {
      if (!context_.hasSameType(left->getReturnType(), right->getReturnType()) ||
          left->getNumParams() != right->getNumParams())
        return false;
      for (unsigned index = 0; index < left->getNumParams(); ++index)
        if (!context_.hasSameType(left->getParamDecl(index)->getType(),
                                  right->getParamDecl(index)->getType()))
          return false;
      return true;
    };
    llvm::json::Array overrides;
    for (const clang::CXXMethodDecl *overridden : method->overridden_methods()) {
      if (!same_signature(method, overridden)) {
        fail(method->getLocation(),
             "a C++ override with a covariant result remains unsupported");
        return std::nullopt;
      }
      const clang::FunctionDecl *target = virtual_target(overridden);
      if (target == nullptr || !remember_function(target))
        return std::nullopt;
      llvm::json::Object reference;
      reference["declaration_id"] = declaration_id(target);
      reference["name"] = method_name(llvm::cast<clang::CXXMethodDecl>(target));
      reference["span"] = span(overridden->getNameInfo().getSourceRange());
      overrides.push_back(std::move(reference));
    }
    llvm::json::Array overridden_by;
    static const std::vector<const clang::CXXMethodDecl *> no_overriders;
    const auto found = overriders_.find(method->getCanonicalDecl());
    for (const clang::CXXMethodDecl *candidate :
         found == overriders_.end() ? no_overriders : found->second) {
      const clang::FunctionDecl *target = virtual_target(candidate);
      if (target == nullptr)
        return std::nullopt;
      if (!executable_source(source_manager_.getSpellingLoc(target->getLocation()))) {
        fail(candidate->getLocation(),
             "an override of a reachable virtual method must be in the selected or "
             "dependency sources");
        return std::nullopt;
      }
      if (!remember_function(target))
        return std::nullopt;
      llvm::json::Object reference;
      reference["declaration_id"] = declaration_id(target);
      reference["name"] = method_name(llvm::cast<clang::CXXMethodDecl>(target));
      reference["span"] = span(candidate->getNameInfo().getSourceRange());
      overridden_by.push_back(std::move(reference));
    }
    llvm::json::Object result;
    result["pure"] = method->isPureVirtual();
    result["overrides"] = std::move(overrides);
    result["overridden_by"] = std::move(overridden_by);
    return Json(std::move(result));
  }

  // The declaration a virtual method is exported from: its definition, or,
  // for a pure virtual method, its declaration.
  const clang::FunctionDecl *virtual_target(const clang::CXXMethodDecl *method) {
    if (method->isPureVirtual())
      return method->getCanonicalDecl();
    const clang::FunctionDecl *definition = method->getDefinition();
    if (definition == nullptr)
      fail(method->getLocation(), "a C++ virtual method has no reachable definition");
    return definition;
  }

  const clang::CXXRecordDecl *complete_record_type(
      clang::QualType type, clang::SourceLocation location) {
    const auto *record_type = type->getAs<clang::RecordType>();
    // Clang may leave an unused specialization uninstantiated. Complete only
    // this reachable type before querying its declaration or layout.
    if (record_type->getDecl()->getDefinition() == nullptr &&
        compiler_.getSema().RequireCompleteType(
            location, type, clang::diag::err_incomplete_type)) {
      fail(location, "the supported C++ record type must be complete");
      return nullptr;
    }
    const auto *record = llvm::dyn_cast_or_null<clang::CXXRecordDecl>(
        record_type->getDecl()->getDefinition());
    if (record == nullptr) {
      fail(location, "the supported C++ record type must be complete");
    }
    return record;
  }

  std::optional<Json> lower_parameter(const clang::ParmVarDecl *parameter) {
    if (std_function_prototype(parameter->getType()) != nullptr) {
      const auto *reference = parameter->getType()->getAs<clang::LValueReferenceType>();
      if (reference != nullptr && !reference->getPointeeType().isConstQualified()) {
        fail(parameter->getLocation(),
             "a C++ std::function parameter is taken by value or by const reference");
        return std::nullopt;
      }
      auto value_type = lower_type(parameter->getType(), parameter->getLocation());
      if (!value_type)
        return std::nullopt;
      llvm::json::Object result;
      result["declaration_id"] = declaration_id(parameter);
      result["name"] = parameter->getNameAsString();
      result["value_type"] = std::move(*value_type);
      result["span"] = span(parameter->getSourceRange());
      return Json(std::move(result));
    }
    const auto *reference =
        parameter->getType()->getAs<clang::LValueReferenceType>();
    const bool int_reference =
        reference != nullptr &&
        !reference->getPointeeType().isVolatileQualified() &&
        !reference->getPointeeType().isRestrictQualified() &&
        (supported_pointer_element(reference->getPointeeType()) ||
         (reference->getPointeeType()->isSignedIntegerType() &&
          reference->getPointeeType().isConstQualified() &&
          context_.getTypeSize(reference->getPointeeType()) == 64));
    const clang::CXXRecordDecl *record_reference = nullptr;
    if (reference != nullptr &&
        !reference->getPointeeType().isVolatileQualified() &&
        !reference->getPointeeType().isRestrictQualified()) {
      if (reference->getPointeeType()->getAs<clang::RecordType>() != nullptr) {
        record_reference = complete_record_type(reference->getPointeeType(),
                                                parameter->getLocation());
        if (record_reference == nullptr) {
          return std::nullopt;
        }
      }
    }
    const auto *pointer = parameter->getType()->getAs<clang::PointerType>();
    const bool mutable_int_pointer =
        pointer != nullptr && !parameter->getType().hasQualifiers() &&
        !pointer->getPointeeType().hasQualifiers() &&
        supported_pointer_element(pointer->getPointeeType());
    const bool by_value_integer =
        !parameter->getType().hasQualifiers() &&
        supported_scalar_value_type(parameter->getType());
    const bool by_value_bool =
        reference == nullptr &&
        context_.hasSameType(parameter->getType().getUnqualifiedType(),
                             context_.BoolTy) &&
        !parameter->getType().isConstQualified();
    const auto *by_value_record = parameter->getType()->getAsCXXRecordDecl();
    const bool trivial_record_value = by_value_record != nullptr &&
        !parameter->getType().hasQualifiers() &&
        by_value_record->isTriviallyCopyable() &&
        by_value_record->hasTrivialCopyConstructor() &&
        by_value_record->hasTrivialDestructor();
    const bool function_pointer =
        !parameter->getType().hasQualifiers() &&
        function_pointer_prototype(parameter->getType()) != nullptr;
    const auto *pointed_record = record_pointer_target(parameter->getType());
    if (!int_reference && record_reference == nullptr && !mutable_int_pointer &&
        !by_value_bool && !by_value_integer && !trivial_record_value &&
        !function_pointer && pointed_record == nullptr) {
      fail(parameter->getLocation(),
           "the supported C++ parameter must be a by-value bool or "
           "signed/unsigned "
           "32/64/128-bit integer or unsigned char, a native element "
           "reference (int, unsigned int, unsigned char or std::byte, possibly const), a const signed-64 reference, or mutable int* parameter, mutable unsigned int*/unsigned char* parameter, or a "
           "mutable or const simple-record reference parameter, a trivially copied simple-record value, "
           "a mutable pointer to a simple record, or a pointer to a noexcept function");
      return std::nullopt;
    }
    if (pointed_record != nullptr && !remember_record(pointed_record)) {
      return std::nullopt;
    }
    if (record_reference != nullptr && !remember_record(record_reference)) {
      return std::nullopt;
    }
    if (trivial_record_value && !remember_record(by_value_record)) {
      return std::nullopt;
    }
    const clang::TypedefNameDecl *source_alias =
        direct_source_alias(parameter->getTypeSourceInfo());
    auto value_type = lower_type(parameter->getType(), parameter->getLocation(),
                                 source_alias);
    if (!value_type) {
      return std::nullopt;
    }
    llvm::json::Object result;
    result["declaration_id"] = declaration_id(parameter);
    result["name"] = parameter->getNameAsString();
    result["value_type"] = std::move(*value_type);
    result["span"] = span(parameter->getSourceRange());
    if (!state_.error.empty()) {
      return std::nullopt;
    }
    return Json(std::move(result));
  }

  const clang::TypedefNameDecl *
  direct_source_alias(const clang::TypeSourceInfo *source) const {
    if (source == nullptr) {
      return nullptr;
    }
    for (clang::TypeLoc location = source->getTypeLoc(); !location.isNull();
         location = location.getNextTypeLoc()) {
      if (const auto alias_location = location.getAs<clang::TypedefTypeLoc>()) {
        return alias_location.getTypedefNameDecl();
      }
    }
    return nullptr;
  }

  // A `[[no_unique_address]]` member of an empty, trivially copyable and
  // destructible class, such as libstdc++'s static-extent storage in
  // `std::span<T, N>`, occupies no bytes and holds no state. It is left out
  // of the record's fields.
  bool stateless_field(const clang::FieldDecl *field) const {
    const auto *type = field->getType()->getAsCXXRecordDecl();
    return field->hasAttr<clang::NoUniqueAddressAttr>() && !field->isBitField() &&
        !field->getType().hasQualifiers() && type != nullptr &&
        type->getDefinition() != nullptr && type->getDefinition()->isEmpty() &&
        type->getDefinition()->isTriviallyCopyable() &&
        type->getDefinition()->hasTrivialDestructor();
  }

  bool has_stateless_field(const clang::CXXRecordDecl *record) const {
    for (const clang::FieldDecl *field : record->fields())
      if (stateless_field(field)) return true;
    return false;
  }

  bool supported_pointer_element(clang::QualType type) const {
    const auto unqualified = type.getUnqualifiedType();
    return !type.isVolatileQualified() && !type.isRestrictQualified() &&
        (context_.hasSameType(unqualified, context_.IntTy) ||
         context_.hasSameType(unqualified, context_.UnsignedIntTy) ||
         context_.hasSameType(unqualified, context_.UnsignedCharTy) ||
         (supported_byte_enum(type) &&
          type->getAs<clang::EnumType>()->getDecl()->getQualifiedNameAsString() == "std::byte"));
  }

  // A mutable pointer to a simple, complete, non-polymorphic record, such
  // as a list node's `Node* next`: its value is the record's address or
  // null, and `p->field` reads the record it points to.
  const clang::CXXRecordDecl *record_pointer_target(clang::QualType type) const {
    const auto *pointer = type->getAs<clang::PointerType>();
    if (pointer == nullptr || type.hasQualifiers() ||
        pointer->getPointeeType().hasQualifiers())
      return nullptr;
    const auto *record = pointer->getPointeeType()->getAsCXXRecordDecl();
    record = record == nullptr ? nullptr : record->getDefinition();
    if (record == nullptr || record->isPolymorphic() || record->getNumBases() != 0)
      return nullptr;
    return record;
  }

  bool supported_byte_pointer_cast(const clang::CastExpr *cast) const {
    const auto *source = cast->getSubExpr()->getType()->getAs<clang::PointerType>();
    const auto *target = cast->getType()->getAs<clang::PointerType>();
    return llvm::isa<clang::CXXReinterpretCastExpr>(cast) &&
        cast->getCastKind() == clang::CK_BitCast && source && target &&
        !source->getPointeeType().hasQualifiers() &&
        !target->getPointeeType().hasQualifiers() &&
        supported_pointer_element(source->getPointeeType()) &&
        supported_byte_enum(target->getPointeeType()) &&
        target->getPointeeType()->getAs<clang::EnumType>()->getDecl()->getQualifiedNameAsString() == "std::byte";
  }

  bool supported_integer_type(clang::QualType type) const {
    return type->isIntegerType() &&
        (context_.hasSameType(type.getUnqualifiedType(), context_.UnsignedCharTy) ||
         context_.getTypeSize(type) == 32 || context_.getTypeSize(type) == 64 ||
         context_.getTypeSize(type) == 128);
  }

  bool supported_byte_enum(clang::QualType type) const {
    const auto *enumeration = type->getAs<clang::EnumType>();
    if (enumeration == nullptr) return false;
    const auto *declaration = enumeration->getDecl()->getDefinition();
    return declaration != nullptr && declaration->isScoped() && declaration->isFixed() &&
        context_.hasSameType(declaration->getIntegerType(), context_.UnsignedCharTy);
  }

  bool supported_scalar_value_type(clang::QualType type) const {
    return supported_integer_type(type) || supported_byte_enum(type);
  }

  // The call signature of `std::function<R(A...)>`, possibly const or behind
  // an lvalue reference, when `type` is one. Click models it as a callable
  // value, not as the library's record: a contract on it says what calling
  // it does, and implies it is not empty.
  const clang::FunctionProtoType *
  std_function_prototype(clang::QualType type) const {
    if (const auto *reference = type->getAs<clang::LValueReferenceType>())
      type = reference->getPointeeType();
    const auto *specialization =
        llvm::dyn_cast_or_null<clang::ClassTemplateSpecializationDecl>(
            type->getAsCXXRecordDecl());
    if (specialization == nullptr || !specialization->isInStdNamespace() ||
        specialization->getName() != "function" ||
        specialization->getTemplateArgs().size() != 1 ||
        specialization->getTemplateArgs()[0].getKind() != clang::TemplateArgument::Type)
      return nullptr;
    return specialization->getTemplateArgs()[0]
        .getAsType()
        ->getAs<clang::FunctionProtoType>();
  }

  // The function type a pointer designates, when `type` is a pointer to a
  // function, as in `int (*)(int) noexcept`.
  const clang::FunctionProtoType *
  function_pointer_prototype(clang::QualType type) const {
    const auto *pointer = type->getAs<clang::PointerType>();
    return pointer == nullptr
               ? nullptr
               : pointer->getPointeeType()->getAs<clang::FunctionProtoType>();
  }

  // A value a function reached through a pointer takes or returns: a bool,
  // a supported integer, or a mutable pointer to a native element.
  bool supported_callback_value(clang::QualType type) const {
    if (type.hasQualifiers())
      return false;
    if (context_.hasSameType(type, context_.BoolTy) ||
        supported_scalar_value_type(type))
      return true;
    const auto *pointer = type->getAs<clang::PointerType>();
    return pointer != nullptr && !pointer->getPointeeType().hasQualifiers() &&
           supported_pointer_element(pointer->getPointeeType());
  }

  // A pointer to a non-throwing, non-variadic function whose parameters and
  // result are scalars or native element pointers. A call through one
  // cannot throw, so it needs no exceptional contract.
  std::optional<Json> lower_function_pointer_type(clang::QualType type,
                                                  clang::SourceLocation location) {
    // A `std::function` is not `noexcept`: its target is, as every verified
    // function is outside the exception profile, and a contract on it says
    // it holds one.
    const auto *standard = std_function_prototype(type);
    const auto *prototype = standard != nullptr ? standard : function_pointer_prototype(type);
    if (type.isVolatileQualified() || type.isRestrictQualified() ||
        prototype->isVariadic() || (standard == nullptr && !prototype->isNothrow()) ||
        prototype->getMethodQuals().hasQualifiers() ||
        prototype->getRefQualifier() != clang::RQ_None) {
      fail(location, "a C++ function pointer must point to a noexcept, non-variadic function");
      return std::nullopt;
    }
    if (!prototype->getReturnType()->isVoidType() &&
        !supported_callback_value(prototype->getReturnType())) {
      fail(location, "a C++ function pointer's function must return void, bool, a "
                     "supported integer or a native element pointer");
      return std::nullopt;
    }
    auto return_type = lower_type(prototype->getReturnType(), location);
    if (!return_type)
      return std::nullopt;
    llvm::json::Array parameters;
    for (clang::QualType parameter : prototype->getParamTypes()) {
      if (!supported_callback_value(parameter)) {
        fail(location, "a C++ function pointer's function must take bool, supported "
                       "integer or native element pointer parameters");
        return std::nullopt;
      }
      auto lowered = lower_type(parameter, location);
      if (!lowered)
        return std::nullopt;
      parameters.push_back(std::move(*lowered));
    }
    llvm::json::Object result;
    result["kind"] = "function_pointer";
    result["return_type"] = std::move(*return_type);
    result["parameters"] = std::move(parameters);
    result["is_const"] = standard == nullptr && type.isConstQualified();
    return Json(std::move(result));
  }

  std::optional<Json>
  lower_type(clang::QualType type, clang::SourceLocation location,
             const clang::TypedefNameDecl *source_alias = nullptr) {
    if (std_function_prototype(type) != nullptr)
      return lower_function_pointer_type(type, location);
    if (type->isVoidType()) {
      llvm::json::Object result;
      result["kind"] = "void";
      return Json(std::move(result));
    }
    if (const auto *reference = type->getAs<clang::LValueReferenceType>()) {
      auto pointee =
          lower_type(reference->getPointeeType(), location, source_alias);
      if (!pointee) {
        return std::nullopt;
      }
      llvm::json::Object result;
      result["kind"] = "lvalue_reference";
      result["pointee"] = std::move(*pointee);
      return Json(std::move(result));
    }
    // A fixed-length array of a native element; the record profile admits
    // one only as a field, such as `std::array`'s `_M_elems`.
    if (const auto *array = context_.getAsConstantArrayType(type)) {
      auto element = lower_type(array->getElementType(), location);
      if (!element) {
        return std::nullopt;
      }
      llvm::json::Object result;
      result["kind"] = "array";
      result["element"] = std::move(*element);
      result["length"] = static_cast<std::int64_t>(array->getSize().getZExtValue());
      return Json(std::move(result));
    }
    if (function_pointer_prototype(type) != nullptr)
      return lower_function_pointer_type(type, location);
    if (const auto *pointer = type->getAs<clang::PointerType>()) {
      auto pointee = lower_type(pointer->getPointeeType(), location);
      if (!pointee) {
        return std::nullopt;
      }
      llvm::json::Object result;
      result["kind"] = "pointer";
      result["pointee"] = std::move(*pointee);
      return Json(std::move(result));
    }
    // A generic template's abstract type argument is a type parameter: a
    // value of it is only copied.
    if (const std::string *name = archetype_name(type)) {
      if (type.isVolatileQualified() || type.isRestrictQualified()) {
        fail(location, "qualified abstract type arguments are outside the supported slice");
        return std::nullopt;
      }
      llvm::json::Object result;
      result["kind"] = "parameter";
      result["name"] = *name;
      result["is_const"] = type.isConstQualified();
      return Json(std::move(result));
    }
    if (type->getAs<clang::RecordType>() != nullptr) {
      const auto *record = complete_record_type(type, location);
      if (type.isVolatileQualified() || type.isRestrictQualified() ||
          record == nullptr || !remember_record(record)) {
        if (record == nullptr && state_.error.empty()) {
          fail(location, "the supported C++ record type must be complete");
        } else if (type.hasQualifiers() && state_.error.empty()) {
          fail(location,
               "qualified C++ record objects are outside the supported slice");
        }
        return std::nullopt;
      }
      llvm::json::Object result;
      result["kind"] = "record";
      result["declaration_id"] = declaration_id(record);
      result["name"] = record_name(record);
      result["is_const"] = type.isConstQualified();
      return Json(std::move(result));
    }
    if (const auto *enumeration = type->getAs<clang::EnumType>()) {
      if (!supported_byte_enum(type) || type.isVolatileQualified() || type.isRestrictQualified()) {
        fail(location, "C++ enums require a scoped declaration with fixed unsigned-char backing");
        return std::nullopt;
      }
      const auto *declaration = enumeration->getDecl()->getDefinition();
      auto underlying = lower_type(declaration->getIntegerType(), declaration->getLocation());
      if (!underlying) return std::nullopt;
      llvm::json::Object result;
      result["kind"] = "enumeration";
      result["declaration_id"] = declaration_id(declaration);
      result["name"] = declaration->getQualifiedNameAsString();
      result["is_scoped"] = true;
      result["is_fixed"] = true;
      result["is_const"] = type.isConstQualified();
      result["underlying_type"] = std::move(*underlying);
      result["span"] = declaration_span(declaration->getSourceRange());
      return Json(std::move(result));
    }
    if (context_.hasSameType(type.getUnqualifiedType(), context_.BoolTy)) {
      llvm::json::Object result;
      result["kind"] = "boolean";
      result["bits"] = static_cast<std::int64_t>(context_.getTypeSize(type));
      result["is_const"] = type.isConstQualified();
      return Json(std::move(result));
    }
    if (!supported_integer_type(type)) {
      fail(location, "the supported C++ slice supports bool, signed/unsigned "
                     "32/64/128-bit integers, unsigned char, selected signed references, mutable "
                     "int*, and one simple record-reference type");
      return std::nullopt;
    }
    llvm::json::Object result;
    result["kind"] = "integer";
    result["bits"] = static_cast<std::int64_t>(context_.getTypeSize(type));
    result["signed"] = type->isSignedIntegerType();
    result["is_const"] = type.isConstQualified();
    const clang::TypedefNameDecl *alias_declaration = source_alias;
    if (alias_declaration == nullptr) {
      if (const auto *alias =
              llvm::dyn_cast<clang::TypedefType>(type.getTypePtr())) {
        alias_declaration = alias->getDecl();
      }
    }
    llvm::json::Array source_aliases;
    std::unordered_set<const clang::TypedefNameDecl *> seen_aliases;
    while (alias_declaration != nullptr) {
      alias_declaration = alias_declaration->getCanonicalDecl();
      if (!seen_aliases.insert(alias_declaration).second) {
        fail(alias_declaration->getLocation(),
             "C++ type alias chain contains a cycle");
        return std::nullopt;
      }
      llvm::json::Object source_alias;
      source_alias["declaration_id"] = declaration_id(alias_declaration);
      source_alias["name"] = alias_declaration->getNameAsString();
      source_alias["span"] = declaration_span(alias_declaration->getSourceRange());
      if (!state_.error.empty()) {
        return std::nullopt;
      }
      source_aliases.push_back(std::move(source_alias));
      const clang::TypedefNameDecl *next_alias =
          direct_source_alias(alias_declaration->getTypeSourceInfo());
      if (next_alias == alias_declaration) {
        next_alias = nullptr;
      }
      alias_declaration = next_alias;
    }
    result["source_aliases"] = std::move(source_aliases);
    return Json(std::move(result));
  }

  const clang::Expr *library_argument_value(const clang::Expr *expression) const {
    expression = expression->IgnoreParens();
    if (const auto *temporary = llvm::dyn_cast<clang::MaterializeTemporaryExpr>(expression)) {
      expression = temporary->getSubExpr()->IgnoreParens();
    }
    return expression;
  }

  std::optional<Json> consteval_metadata(const clang::Expr *argument,
                                        clang::QualType parameter_type, unsigned index) {
    const clang::Expr *expression = library_argument_value(argument->IgnoreParenImpCasts())->IgnoreParenImpCasts();
    if (const auto *constant = llvm::dyn_cast<clang::ConstantExpr>(expression)) {
      expression = constant->getSubExpr()->IgnoreParenImpCasts();
    }
    const auto *call = llvm::dyn_cast<clang::CallExpr>(expression);
    const auto *callee = call == nullptr ? nullptr : call->getDirectCallee();
    const clang::QualType value_type = parameter_type.getNonReferenceType();
    bool safe_type = value_type->isIntegerType() && !value_type.isVolatileQualified();
    if (const auto *record_type = value_type->getAs<clang::RecordType>()) {
      const auto *record = llvm::dyn_cast_or_null<clang::CXXRecordDecl>(record_type->getDecl()->getDefinition());
      safe_type = parameter_type->isLValueReferenceType() && value_type.isConstQualified() &&
                  !value_type.isVolatileQualified() && record && record->hasTrivialDestructor();
    } else if (parameter_type->isReferenceType()) {
      safe_type = safe_type && parameter_type->isLValueReferenceType() && value_type.isConstQualified();
    }
    if (!safe_type || !call || !callee || !callee->isConsteval() ||
        !call->isPRValue() || !call->isCXX11ConstantExpr(context_) ||
        !context_.hasSameUnqualifiedType(call->getType(), value_type)) {
      fail(argument->getExprLoc(), "C++ library metadata argument " + std::to_string(index) + " requires a forced consteval prvalue of the exact parameter type, with trivial cleanup; records bind only to const references");
      return std::nullopt;
    }
    std::filesystem::path file(source_manager_.getFilename(
        source_manager_.getSpellingLoc(callee->getLocation())).str());
    if (file.empty()) {
      fail(argument->getExprLoc(), "C++ consteval metadata requires a file-backed declaration");
      return std::nullopt;
    }
    if (file.is_relative()) file = std::filesystem::path(compilation_directory_) / file;
    std::error_code error;
    file = std::filesystem::canonical(file, error);
    if (error) {
      fail(argument->getExprLoc(), "could not resolve C++ consteval metadata declaration");
      return std::nullopt;
    }
    llvm::json::Object result;
    result["kind"] = "consteval";
    result["function"] = callee->getQualifiedNameAsString();
    result["declaration_file"] = file.generic_string();
    return Json(std::move(result));
  }

  std::optional<Json> literal_metadata(const clang::CXXConstructExpr *expression,
                                       clang::QualType parameter_type,
                                       const llvm::json::Object &contract,
                                       unsigned index) {
    const auto *pin = contract.getObject("literal_constructor");
    const auto *constructor = expression->getConstructor();
    const auto *record = constructor->getParent();
    const clang::QualType value_type = parameter_type.getNonReferenceType();
    const bool by_value = !parameter_type->isReferenceType();
    const bool const_reference = parameter_type->isLValueReferenceType() && value_type.isConstQualified();
    const clang::QualType pointer_type = constructor->getNumParams() == 1 ? constructor->getParamDecl(0)->getType() : clang::QualType{};
    const bool literal_signature = !pointer_type.isNull() && pointer_type->isPointerType() &&
        pointer_type->getPointeeType().isConstQualified() &&
        !pointer_type->getPointeeType().isVolatileQualified() &&
        context_.hasSameUnqualifiedType(pointer_type->getPointeeType(), context_.CharTy);
    const auto *decay = expression->getNumArgs() == 1 ? llvm::dyn_cast<clang::ImplicitCastExpr>(expression->getArg(0)->IgnoreParens()) : nullptr;
    const auto *literal = decay && decay->getCastKind() == clang::CK_ArrayToPointerDecay ? llvm::dyn_cast<clang::StringLiteral>(decay->getSubExpr()->IgnoreParens()) : nullptr;
    const bool safe_literal = literal && literal->isOrdinary() && literal->getBytes().size() <= 4096 &&
        std::all_of(literal->getBytes().begin(), literal->getBytes().end(), [](unsigned char byte) { return byte > 0 && byte < 128; });
    if (!pin || !pin->getString("function") || !pin->getString("header") || !pin->getString("sha256") ||
        record->getQualifiedNameAsString() + "::" + record->getNameAsString() != pin->getString("function") ||
        constructor->isVariadic() || pointer_type.isVolatileQualified() || !literal_signature || !safe_literal ||
        !expression->isPRValue() || !context_.hasSameUnqualifiedType(expression->getType(), value_type) ||
        value_type.isVolatileQualified() || !(by_value || const_reference) ||
        !record->hasTrivialDestructor() || (by_value && !record->hasTrivialCopyConstructor())) {
      fail(expression->getExprLoc(), "C++ library metadata argument " + std::to_string(index) + " requires an explicitly pinned narrow-literal constructor, exact record type, and trivial initialization/cleanup");
      return std::nullopt;
    }
    const std::string header = pin->getString("header")->str();
    auto declaration_header = dependency_source(constructor->getLocation());
    const auto *definition = constructor->getDefinition();
    if ((definition && is_in_logical_source(definition->getLocation())) ||
        !declaration_header || *declaration_header != header ||
        (definition && dependency_source(definition->getLocation()) != declaration_header)) {
      fail(expression->getExprLoc(), "C++ literal metadata constructor differs from its pinned external header");
      return std::nullopt;
    }
    std::filesystem::path file(source_manager_.getFilename(source_manager_.getSpellingLoc(constructor->getLocation())).str());
    if (file.is_relative()) file = std::filesystem::path(compilation_directory_) / file;
    std::error_code error;
    file = std::filesystem::canonical(file, error);
    if (error) {
      fail(expression->getExprLoc(), "could not resolve C++ literal metadata constructor declaration");
      return std::nullopt;
    }
    dependency_sources_.insert(header);
    llvm::json::Object result;
    result["kind"] = "literal";
    result["constructor"] = Json(llvm::json::Object(*pin));
    result["declaration_file"] = file.generic_string();
    result["record"] = record->getQualifiedNameAsString();
    result["record_type"] = value_type.getCanonicalType().getUnqualifiedType().getAsString();
    result["literal"] = literal->getBytes().str();
    result["binding"] = by_value ? "value" : "const_reference";
    return Json(std::move(result));
  }

  std::optional<Json> lower_library_assertion(
      const clang::CallExpr *call, const clang::FunctionDecl *callee,
      const clang::FunctionDecl *function, const llvm::json::Value &contract) {
    const auto *object = contract.getAsObject();
    const std::string header = object->getString("header")->str();
    auto declaration_header = dependency_source(callee->getLocation());
    const auto *definition = callee->getDefinition();
    if (definition && is_in_logical_source(definition->getLocation())) {
      fail(call->getExprLoc(), "selected-source C++ definitions require ordinary verified contracts, not assumed library assertions");
      return std::nullopt;
    }
    if (!declaration_header || *declaration_header != header ||
        (definition && dependency_source(definition->getLocation()) != declaration_header)) {
      fail(call->getExprLoc(), "C++ assumed library assertion declaration differs from its pinned header");
      return std::nullopt;
    }
    const bool forwarding = object->getString("kind") != "checked_boolean_statement";
    const clang::QualType parameter = callee->getNumParams() == 0 ? clang::QualType{} : callee->getParamDecl(0)->getType();
    const clang::QualType returned = callee->getReturnType();
    const clang::Expr *argument = call->getNumArgs() == 0 ? nullptr : library_argument_value(call->getArg(0));
    const bool valid_parameter = !parameter.isNull() &&
        (parameter->isBooleanType() || (forwarding && parameter->isRValueReferenceType() && parameter.getNonReferenceType()->isBooleanType())) &&
        !parameter.getNonReferenceType().isVolatileQualified();
    const bool valid_return = returned->isVoidType() || returned->isBooleanType() ||
        (forwarding && returned->isRValueReferenceType() && returned.getNonReferenceType()->isBooleanType());
    if (llvm::isa<clang::CXXMethodDecl>(callee) || (!forwarding && callee->getPrimaryTemplate()) ||
        callee->isVariadic() || callee->getNumParams() != call->getNumArgs() ||
        call->getNumArgs() == 0 || call->getNumArgs() > (forwarding ? 9u : 1u) ||
        !valid_parameter || !valid_return || !argument || !argument->getType()->isBooleanType() ||
        (parameter->isRValueReferenceType() && !argument->isPRValue()) ||
        !checked_boolean_condition(argument, function, true)) {
      fail(call->getExprLoc(), "C++ assumed library assertion requires a supported Boolean statement signature and one supported scalar Boolean condition (field reads are checked during evaluation)");
      return std::nullopt;
    }
    llvm::json::Array metadata;
    for (unsigned index = 1; index < call->getNumArgs(); ++index) {
      const clang::Expr *metadata_argument = library_argument_value(call->getArg(index));
      if (const auto *conversion = llvm::dyn_cast<clang::ImplicitCastExpr>(metadata_argument)) {
        if (conversion->getCastKind() == clang::CK_ConstructorConversion) metadata_argument = conversion->getSubExpr()->IgnoreParens();
      }
      const auto *construction = llvm::dyn_cast<clang::CXXConstructExpr>(metadata_argument);
      auto value = construction && object->getString("kind") == "checked_boolean_statement_with_literal_metadata"
          ? literal_metadata(construction, callee->getParamDecl(index)->getType(), *object, index)
          : consteval_metadata(call->getArg(index), callee->getParamDecl(index)->getType(), index);
      if (!value) return std::nullopt;
      metadata.push_back(std::move(*value));
    }
    auto condition = lower_expression(argument, function);
    if (!condition) return std::nullopt;
    dependency_sources_.insert(header);
    llvm::json::Object result;
    result["kind"] = "library_assert";
    result["condition"] = std::move(*condition);
    result["contract"] = contract;
    result["metadata"] = std::move(metadata);
    result["specialization"] = callee->getPrimaryTemplate() ? Json(function_name(callee)) : Json(nullptr);
    result["span"] = span(clang::SourceRange(
        source_manager_.getExpansionLoc(call->getBeginLoc()),
        source_manager_.getExpansionLoc(call->getEndLoc())));
    return Json(std::move(result));
  }

  const clang::Stmt *without_branch_weights(const clang::Stmt *statement) {
    while (const auto *attributed = llvm::dyn_cast<clang::AttributedStmt>(statement)) {
      // These attributes affect optimization weights only. Other statement
      // attributes can alter execution contracts and must not be erased.
      for (const auto *attribute : attributed->getAttrs()) {
        if (!llvm::isa<clang::LikelyAttr, clang::UnlikelyAttr>(attribute)) {
          fail(attribute->getLocation(), "unsupported C++ statement attribute; only likely/unlikely branch weights are admitted");
          return nullptr;
        }
      }
      statement = attributed->getSubStmt();
    }
    return statement;
  }

  std::optional<Json> lower_statement(const clang::Stmt *statement,
                                      const clang::FunctionDecl *function,
                                      bool allow_local_declaration,
                                      bool allow_nested_scope) {
    statement = without_branch_weights(statement);
    if (!statement) return std::nullopt;
    if (const auto *loop = llvm::dyn_cast<clang::DoStmt>(statement)) {
      // A literal-false do loop executes its body once. Do not fold runtime
      // conditions or erase control transfers; lower_branch still rejects
      // unsupported break/continue and local-lifetime arrangements.
      const auto *condition = loop->getCond()->IgnoreParenImpCasts();
      const auto *boolean = llvm::dyn_cast<clang::CXXBoolLiteralExpr>(condition);
      const auto *integer = llvm::dyn_cast<clang::IntegerLiteral>(condition);
      if (!((boolean && !boolean->getValue()) ||
            (integer && integer->getValue().isZero()))) {
        fail(loop->getDoLoc(),
             "C++ do loops require a literal false condition; runtime and repeated loops remain unsupported");
        return std::nullopt;
      }
      auto body = lower_branch(loop->getBody(), function, CleanupScopeKind::None);
      if (!body) return std::nullopt;
      llvm::json::Object result;
      result["kind"] = "if";
      result["condition"] = boolean_constant(true, loop->getCond()->getSourceRange(), true);
      result["then_branch"] = std::move(*body);
      result["else_branch"] = llvm::json::Array();
      result["span"] = span(loop->getSourceRange());
      return Json(std::move(result));
    }
    if (const auto *cleanups = llvm::dyn_cast<clang::ExprWithCleanups>(statement)) {
      const auto *call = llvm::dyn_cast<clang::CallExpr>(cleanups->getSubExpr());
      const auto *callee = call == nullptr ? nullptr : call->getDirectCallee();
      // A trivial record assignment still materializes the RHS temporary. Its
      // lifetime is represented by the explicit assignment operation below.
      if (const auto *operation = llvm::dyn_cast_or_null<clang::CXXOperatorCallExpr>(call);
          operation != nullptr && operation->getOperator() == clang::OO_Equal &&
          !cleanups->cleanupsHaveSideEffects()) {
        return lower_statement(operation, function, allow_local_declaration, allow_nested_scope);
      }
      if (callee) {
        auto contract = library_assertions_.find(callee->getQualifiedNameAsString());
        if (contract != library_assertions_.end() &&
            contract->second.getAsObject()->getString("kind") != "checked_boolean_statement") {
          if (cleanups->cleanupsHaveSideEffects()) {
            fail(cleanups->getExprLoc(), "C++ library assertion cannot erase temporary cleanup effects");
            return std::nullopt;
          }
          return lower_library_assertion(call, callee, function, contract->second);
        }
      }
    }
    if (const auto *throw_expression =
            llvm::dyn_cast<clang::CXXThrowExpr>(statement)) {
      if (exception_behavior_ != "scalar_int32") {
        fail(throw_expression->getThrowLoc(),
             "throw expressions are outside the normal-only C++ profile");
        return std::nullopt;
      }
      const clang::Expr *payload = throw_expression->getSubExpr();
      if (payload == nullptr) {
        fail(throw_expression->getThrowLoc(),
             "rethrow is outside the scalar int32 exception profile");
        return std::nullopt;
      }
      if (!payload->getType()->isSpecificBuiltinType(clang::BuiltinType::Int)) {
        fail(throw_expression->getThrowLoc(),
             "scalar exception payload must have type int32");
        return std::nullopt;
      }
      auto value = lower_expression(payload, function);
      if (!value) {
        return std::nullopt;
      }
      llvm::json::Object result;
      result["kind"] = "throw";
      result["value"] = std::move(*value);
      result["span"] = span(throw_expression->getSourceRange());
      return Json(std::move(result));
    }
    if (const auto *try_statement = llvm::dyn_cast<clang::CXXTryStmt>(statement)) {
      if (exception_behavior_ != "scalar_int32") {
        fail(try_statement->getTryLoc(),
             "try/catch is outside the normal-only C++ profile");
        return std::nullopt;
      }
      if (!allow_nested_scope) {
        fail(try_statement->getTryLoc(),
             "nested try/catch is outside the scalar int32 exception profile");
        return std::nullopt;
      }
      return lower_try_catch_int32(try_statement, function);
    }
    if (const auto *declaration = llvm::dyn_cast<clang::DeclStmt>(statement)) {
      if (!allow_local_declaration) {
        fail(declaration->getBeginLoc(),
             "automatic C++ locals are currently supported only in the function body");
        return std::nullopt;
      }
      return lower_local_declaration(declaration, function,
                                     allow_nested_scope);
    }
    if (const auto *compound = llvm::dyn_cast<clang::CompoundStmt>(statement)) {
      if (!allow_nested_scope || llvm::isa<clang::CXXMethodDecl>(function)) {
        fail(compound->getLBracLoc(),
             "the supported C++ slice permits one nested scope directly in a free-function body");
        return std::nullopt;
      }
      return lower_scope(compound, function, false);
    }
    if (const auto *call = llvm::dyn_cast<clang::CallExpr>(statement)) {
      if (const auto *operation = llvm::dyn_cast<clang::CXXOperatorCallExpr>(call);
          operation != nullptr && operation->getOperator() == clang::OO_Equal &&
          operation->getNumArgs() == 2 &&
          archetype_name(operation->getArg(0)->getType()) != nullptr)
        return lower_archetype_assignment(operation, function);
      if (const auto *operation = llvm::dyn_cast<clang::CXXOperatorCallExpr>(call);
          operation != nullptr && operation->getOperator() == clang::OO_Equal) {
        const auto *method =
            llvm::dyn_cast_or_null<clang::CXXMethodDecl>(operation->getDirectCallee());
        const clang::Expr *assignment_rhs = operation->getNumArgs() == 2
            ? operation->getArg(1)->IgnoreParens() : nullptr;
        // IgnoreParenImpCasts also erases materialization wrappers. Retain that
        // lifetime evidence while stripping only implicit qualification casts.
        while (const auto *cast = llvm::dyn_cast_or_null<clang::ImplicitCastExpr>(assignment_rhs))
          assignment_rhs = cast->getSubExpr()->IgnoreParens();
        if (method != nullptr && method->isCopyAssignmentOperator() &&
            method->isTrivial() && !method->isDeleted() && !method->isVirtual() &&
            method->getParent()->hasTrivialDestructor() && operation->getNumArgs() == 2 &&
            operation->getArg(0)->isLValue() && operation->getArg(1)->isLValue() &&
            !llvm::isa_and_nonnull<clang::MaterializeTemporaryExpr>(assignment_rhs)) {
          auto target = lower_place_reference(operation->getArg(0)->IgnoreParenImpCasts(), function);
          auto source = lower_place_reference(operation->getArg(1)->IgnoreParenImpCasts(), function);
          if (!target || !source) return std::nullopt;
          llvm::json::Object result;
          result["kind"] = "trivial_copy";
          result["target"] = std::move(*target);
          result["source"] = std::move(*source);
          result["span"] = span(operation->getSourceRange());
          return Json(std::move(result));
        }
        if (method != nullptr && method->isCopyAssignmentOperator() &&
            method->isTrivial() && !method->isDeleted() && !method->isVirtual() &&
            method->getParent()->isTriviallyCopyable() &&
            method->getParent()->hasTrivialDestructor() && operation->getNumArgs() == 2 &&
            operation->getArg(0)->isLValue()) {
          const auto *temporary = llvm::dyn_cast_or_null<clang::MaterializeTemporaryExpr>(assignment_rhs);
          const auto *rhs = temporary == nullptr ? nullptr : llvm::dyn_cast<clang::CallExpr>(
              temporary->getSubExpr()->IgnoreParenImpCasts());
          if (rhs != nullptr && rhs->isPRValue() &&
              temporary->getStorageDuration() == clang::SD_FullExpression &&
              context_.hasSameUnqualifiedType(rhs->getType(), operation->getArg(0)->getType())) {
            auto target = lower_place_reference(operation->getArg(0)->IgnoreParenImpCasts(), function);
            auto value_type = lower_type(rhs->getType(), rhs->getExprLoc());
            auto call = lower_call_operation(rhs, function, true);
            if (!target || !value_type || !call) return std::nullopt;
            llvm::json::Object result;
            result["kind"] = "assign_construction_call";
            result["target"] = std::move(*target);
            result["value_type"] = std::move(*value_type);
            result["callee"] = std::move(call->callee);
            result["arguments"] = std::move(call->arguments);
            result["span"] = span(operation->getSourceRange());
            return Json(std::move(result));
          }
        }
        fail(operation->getExprLoc(),
             "C++ record assignment requires a trivial copy assignment between live lvalues or from a full-expression construction-call temporary with trivial destruction");
        return std::nullopt;
      }
      const auto *callee = call->getDirectCallee();
      if (callee != nullptr) {
        auto contract = library_assertions_.find(callee->getQualifiedNameAsString());
        if (contract != library_assertions_.end()) {
          return lower_library_assertion(call, callee, function, contract->second);
        }
      }
      if (callee != nullptr && callee->getBuiltinID() == clang::Builtin::BI__builtin_unreachable) {
        if (call->getNumArgs() != 0) {
          fail(call->getExprLoc(), "C++ __builtin_unreachable requires no arguments");
          return std::nullopt;
        }
        llvm::json::Object result;
        result["kind"] = "unreachable";
        result["span"] = span(call->getSourceRange());
        return Json(std::move(result));
      }
      if (callee != nullptr && callee->getBuiltinID() == clang::Builtin::BI__builtin_assume) {
        if (call->getNumArgs() != 1 || !checked_boolean_condition(call->getArg(0), function, false)) {
          fail(call->getExprLoc(), "C++ __builtin_assume requires a total scalar condition without memory reads or side effects");
          return std::nullopt;
        }
        auto condition = lower_expression(call->getArg(0), function);
        if (!condition) return std::nullopt;
        llvm::json::Object result;
        result["kind"] = "assume";
        result["condition"] = std::move(*condition);
        result["span"] = span(call->getSourceRange());
        return Json(std::move(result));
      }
      return lower_call(call, function);
    }
    // `delete p`: the end of one simple record that `new` allocated, whose
    // destruction does nothing. Deleting null does nothing.
    if (const auto *deleted = llvm::dyn_cast<clang::CXXDeleteExpr>(statement)) {
      const auto *record = record_pointer_target(deleted->getArgument()->IgnoreImpCasts()->getType());
      const auto *deallocator = deleted->getOperatorDelete();
      if (deleted->isArrayForm() || record == nullptr || deallocator == nullptr ||
          !deallocator->isReplaceableGlobalAllocationFunction() ||
          !record->hasTrivialDestructor()) {
        fail(deleted->getBeginLoc(),
             "a supported C++ `delete` ends one simple record with trivial destruction "
             "through the global operator delete");
        return std::nullopt;
      }
      auto pointer = lower_expression(deleted->getArgument(), function);
      if (!pointer) return std::nullopt;
      llvm::json::Object result;
      result["kind"] = "delete_object";
      result["pointer"] = std::move(*pointer);
      result["span"] = span(deleted->getSourceRange());
      return Json(std::move(result));
    }
    if (const auto *binary = llvm::dyn_cast<clang::BinaryOperator>(statement)) {
      if (binary->getOpcode() != clang::BO_Assign &&
          binary->getOpcode() != clang::BO_AddAssign &&
          binary->getOpcode() != clang::BO_SubAssign) {
        fail(binary->getOperatorLoc(),
             "the first C++ slice supports only simple assignment statements");
        return std::nullopt;
      }
      if (const auto *created =
              llvm::dyn_cast<clang::CXXNewExpr>(binary->getRHS()->IgnoreParenImpCasts());
          created != nullptr && binary->getOpcode() == clang::BO_Assign) {
        auto target = lower_place_reference(binary->getLHS()->IgnoreParens(), function);
        if (!target) return std::nullopt;
        auto object = lower_new_object(created, function);
        if (!object) return std::nullopt;
        llvm::json::Object result = std::move(*object->getAsObject());
        result["kind"] = "new_object";
        result["target"] = std::move(*target);
        result["span"] = span(binary->getSourceRange());
        return Json(std::move(result));
      }
      auto value = lower_expression(binary->getRHS(), function);
      if (!value) {
        return std::nullopt;
      }
      llvm::json::Object result;
      const clang::Expr *left = binary->getLHS()->IgnoreParens();
      if (binary->getOpcode() == clang::BO_AddAssign ||
          binary->getOpcode() == clang::BO_SubAssign) {
        const auto *compound =
            llvm::cast<clang::CompoundAssignOperator>(binary);
        const auto *member = llvm::dyn_cast<clang::MemberExpr>(left);
        if (member == nullptr ||
            !context_.hasSameType(compound->getComputationLHSType(),
                                  left->getType()) ||
            !context_.hasSameType(compound->getComputationResultType(),
                                  left->getType()) ||
            !context_.hasSameType(binary->getRHS()->getType(),
                                  left->getType()) ||
            !left->getType()->isSignedIntegerType() ||
            context_.getTypeSize(left->getType()) == 128) {
          fail(binary->getOperatorLoc(), "supported C++ += and -= require a "
                                         "direct signed integer field and "
                                         "same-width operands");
          return std::nullopt;
        }
        auto loaded = lower_member(member, function);
        auto value_type = lower_type(left->getType(), left->getExprLoc());
        auto sum_type = lower_type(left->getType(), left->getExprLoc());
        if (!loaded || !value_type || !sum_type)
          return std::nullopt;
        llvm::json::Object load;
        load["kind"] = "member_load";
        load["object"] = std::move(loaded->object);
        load["field"] = std::move(loaded->field);
        load["value_type"] = std::move(*value_type);
        load["span"] = span(left->getSourceRange());
        llvm::json::Object sum;
        sum["kind"] = "binary";
        sum["operator"] =
            binary->getOpcode() == clang::BO_AddAssign ? "add" : "subtract";
        sum["left"] = std::move(load);
        sum["right"] = std::move(*value);
        sum["value_type"] = std::move(*sum_type);
        sum["span"] = span(binary->getSourceRange());
        value = Json(std::move(sum));
      }
      if (const auto *call = llvm::dyn_cast<clang::CallExpr>(left);
          call != nullptr && binary->getOpcode() == clang::BO_Assign) {
        // A store through a returned native reference, as in `s[i] = v`.
        const auto *callee = call->getDirectCallee();
        const auto *reference = callee == nullptr
            ? nullptr
            : callee->getReturnType()->getAs<clang::LValueReferenceType>();
        if (reference == nullptr || !call->isLValue() ||
            reference->getPointeeType().isConstQualified() ||
            !supported_pointer_element(reference->getPointeeType())) {
          fail(call->getExprLoc(), "C++ call stores require a returned mutable native element reference");
          return std::nullopt;
        }
        auto operation = lower_call_operation(call, function, true);
        auto value_type = lower_type(callee->getReturnType(), call->getExprLoc());
        if (!operation || !value_type) {
          return std::nullopt;
        }
        result["kind"] = "call_store";
        result["callee"] = std::move(operation->callee);
        result["arguments"] = std::move(operation->arguments);
        result["value_type"] = std::move(*value_type);
      } else if (const auto *member = llvm::dyn_cast<clang::MemberExpr>(left)) {
        auto lowered = lower_member(member, function);
        if (!lowered) {
          return std::nullopt;
        }
        result["kind"] = "member_store";
        result["object"] = std::move(lowered->object);
        result["field"] = std::move(lowered->field);
      } else if (const auto *dereference =
                     llvm::dyn_cast<clang::UnaryOperator>(left);
          dereference != nullptr && dereference->getOpcode() == clang::UO_Deref) {
        auto pointer = lower_expression(dereference->getSubExpr(), function);
        if (!pointer) {
          return std::nullopt;
        }
        result["kind"] = "store";
        result["pointer"] = std::move(*pointer);
      } else {
        auto target = lower_place_reference(left, function);
        if (!target) {
          return std::nullopt;
        }
        result["kind"] = "assign";
        result["target"] = std::move(*target);
      }
      result["value"] = std::move(*value);
      result["span"] = span(binary->getSourceRange());
      return Json(std::move(result));
    }
    if (const auto *returned = llvm::dyn_cast<clang::ReturnStmt>(statement)) {
      if (returned->getRetValue() == nullptr) {
        fail(returned->getReturnLoc(),
             "the first C++ slice requires an int return value");
        return std::nullopt;
      }
      llvm::json::Object result;
      const auto *reference_return = function->getReturnType()->getAs<clang::LValueReferenceType>();
      if (function->getReturnType()->isRecordType() &&
          archetype_name(function->getReturnType()) == nullptr) {
        const auto *operand = returned->getRetValue()->IgnoreParenImpCasts();
        if (const auto *cast = llvm::dyn_cast<clang::CXXFunctionalCastExpr>(operand);
            cast != nullptr && cast->getCastKind() == clang::CK_ConstructorConversion &&
            context_.hasSameUnqualifiedType(cast->getType(), function->getReturnType()))
          operand = cast->getSubExpr()->IgnoreParenImpCasts();
        const auto *construction = llvm::dyn_cast<clang::CXXConstructExpr>(operand);
        const auto *constructor = construction == nullptr ? nullptr : construction->getConstructor();
        const auto *record = function->getReturnType()->getAsCXXRecordDecl();
        auto value_type = lower_type(function->getReturnType(), returned->getReturnLoc());
        if (!value_type) return std::nullopt;
        if (returned->getNRVOCandidate() != nullptr || record == nullptr ||
            !record->isTriviallyCopyable() || !record->hasTrivialDestructor()) {
          fail(returned->getReturnLoc(), "C++ record return requires trivial copying/destruction without NRVO");
          return std::nullopt;
        }
        if (constructor != nullptr && constructor->isCopyConstructor() &&
            constructor->isTrivial() && !constructor->isDeleted() &&
            construction->getNumArgs() == 1 && construction->getArg(0)->isLValue() &&
            context_.hasSameUnqualifiedType(construction->getType(), function->getReturnType())) {
          auto source = lower_place_reference(construction->getArg(0)->IgnoreParenImpCasts(), function);
          if (!source) return std::nullopt;
          result["kind"] = "return_record";
          result["source"] = std::move(*source);
        } else if (constructor != nullptr && !constructor->isCopyOrMoveConstructor() &&
                   !constructor->isDeleted() &&
                   construction->getConstructionKind() == clang::CXXConstructionKind::Complete &&
                   context_.hasSameUnqualifiedType(construction->getType(), function->getReturnType())) {
          const auto *definition = llvm::dyn_cast_or_null<clang::CXXConstructorDecl>(constructor->getDefinition());
          if (definition == nullptr || !construction->isPRValue() ||
              !record->hasTrivialCopyConstructor() ||
              construction->getNumArgs() != definition->getNumParams()) {
            fail(returned->getReturnLoc(), "C++ returned construction requires a resolved prvalue constructor and trivial copy constructor");
            return std::nullopt;
          }
          llvm::json::Array arguments;
          for (unsigned index = 0; index < construction->getNumArgs(); ++index) {
            const auto *source_argument = construction->getArg(index);
            const auto *nested = llvm::dyn_cast<clang::CallExpr>(source_argument->IgnoreParenImpCasts());
            std::optional<Json> argument;
            if (nested != nullptr && !is_numeric_limits_max_call(nested)) {
              if (definition->getParamDecl(index)->getType()->isReferenceType() ||
                  !context_.hasSameType(source_argument->getType(), definition->getParamDecl(index)->getType())) {
                fail(source_argument->getExprLoc(), "C++ returned constructor call arguments require matching by-value types");
                return std::nullopt;
              }
              auto operation = lower_call_operation(nested, function, true);
              auto type = lower_type(nested->getType(), nested->getExprLoc());
              if (!operation || !type) return std::nullopt;
              llvm::json::Object call_argument;
              call_argument["kind"] = "call";
              call_argument["callee"] = std::move(operation->callee);
              call_argument["arguments"] = std::move(operation->arguments);
              call_argument["value_type"] = std::move(*type);
              call_argument["span"] = std::move(operation->span);
              argument = Json(std::move(call_argument));
            } else {
              argument = lower_call_argument(source_argument, definition->getParamDecl(index), function);
            }
            if (!argument) return std::nullopt;
            arguments.push_back(std::move(*argument));
          }
          if (!remember_function(definition)) return std::nullopt;
          llvm::json::Object reference;
          reference["declaration_id"] = declaration_id(definition);
          reference["name"] = constructor_name(definition);
          reference["span"] = span(operand->getSourceRange());
          result["kind"] = "return_construct";
          result["callee"] = std::move(reference);
          result["arguments"] = std::move(arguments);
        } else if (const auto *call = llvm::dyn_cast<clang::CallExpr>(operand);
                   call != nullptr && call->isPRValue() &&
                   context_.hasSameUnqualifiedType(call->getType(), function->getReturnType())) {
          auto operation = lower_call_operation(call, function, true);
          if (!operation) return std::nullopt;
          result["kind"] = "return_aggregate_call";
          result["callee"] = std::move(operation->callee);
          result["arguments"] = std::move(operation->arguments);
        } else {
          fail(returned->getReturnLoc(), "C++ record return requires a resolved trivial lvalue copy, prvalue constructor or aggregate forwarding call");
          return std::nullopt;
        }
        result["value_type"] = std::move(*value_type);
      } else {
        auto scalar_call = lower_scalar_call_source(returned->getRetValue());
        if (!scalar_call) return std::nullopt;
        const auto *call = scalar_call->call;
        if (call != nullptr) {
          if (!(reference_return != nullptr
                  ? context_.hasSameType(call->getCallReturnType(context_), function->getReturnType()) &&
                    returned->getRetValue()->isLValue() && scalar_call->conversions.empty()
                  : context_.hasSameType(returned->getRetValue()->getType(), function->getReturnType()))) {
            fail(call->getExprLoc(), "C++ return call requires matching final value "
                                     "and caller return types");
            return std::nullopt;
          }
          auto lowered = lower_call_operation(call, function, true);
          auto value_type = lower_type(reference_return != nullptr ? function->getReturnType() : returned->getRetValue()->getType(),
                                       returned->getRetValue()->getExprLoc(),
                                       direct_source_alias(function->getTypeSourceInfo()));
          if (!lowered || !value_type) {
            return std::nullopt;
          }
          result["kind"] = "return_call";
          if (!scalar_call->conversions.empty())
            result["conversions"] = std::move(scalar_call->conversions);
          result["callee"] = std::move(lowered->callee);
          result["arguments"] = std::move(lowered->arguments);
          result["value_type"] = std::move(*value_type);
        } else {
          auto value = reference_return != nullptr
              ? lower_reference_binding(returned->getRetValue(), function->getReturnType(), function)
              : lower_expression(returned->getRetValue(), function);
          if (!value) {
            return std::nullopt;
          }
          result["kind"] = "return";
          result["value"] = std::move(*value);
        }
      }
      llvm::json::Array cleanups;
      const auto cleanup = cleanup_locals_.find(function->getCanonicalDecl());
      if (cleanup != cleanup_locals_.end()) {
        for (auto iterator = cleanup->second.rbegin();
             iterator != cleanup->second.rend(); ++iterator) {
          auto lowered = lower_cleanup(*iterator, returned->getSourceRange());
          if (!lowered) {
            return std::nullopt;
          }
          cleanups.push_back(std::move(*lowered));
        }
      }
      result["cleanups"] = std::move(cleanups);
      result["span"] = span(returned->getSourceRange());
      return Json(std::move(result));
    }
    if (const auto *loop = llvm::dyn_cast<clang::WhileStmt>(statement)) {
      // A runtime loop re-evaluates its condition before each iteration, so
      // the condition is an expression, never a call whose result the
      // lowering would capture once. Its body may declare scalar and
      // pointer locals, which live for one iteration; an object with a
      // destructor would be destroyed at each back edge, which the cleanup
      // model does not describe.
      if (loop->getConditionVariable() != nullptr) {
        fail(loop->getWhileLoc(),
             "the supported C++ while loop cannot declare a condition variable");
        return std::nullopt;
      }
      if (llvm::isa<clang::CallExpr>(loop->getCond()->IgnoreParenImpCasts())) {
        fail(loop->getCond()->getExprLoc(),
             "a C++ while condition is an expression, not a call");
        return std::nullopt;
      }
      auto condition = lower_expression(loop->getCond(), function);
      if (!condition) return std::nullopt;
      ++loop_depth_;
      llvm::json::Array body;
      const auto *compound = llvm::dyn_cast<clang::CompoundStmt>(loop->getBody());
      std::vector<const clang::Stmt *> members;
      if (compound != nullptr)
        members.assign(compound->body_begin(), compound->body_end());
      else
        members.push_back(loop->getBody());
      for (const clang::Stmt *member : members) {
        if (is_checked_runtime_noop(member)) continue;
        auto lowered = lower_statement(member, function, true, false);
        if (!lowered) {
          --loop_depth_;
          return std::nullopt;
        }
        body.push_back(std::move(*lowered));
      }
      --loop_depth_;
      llvm::json::Object result;
      result["kind"] = "while";
      result["condition"] = std::move(*condition);
      result["body"] = std::move(body);
      result["span"] = span(loop->getSourceRange());
      return Json(std::move(result));
    }
    if (const auto *conditional = llvm::dyn_cast<clang::IfStmt>(statement)) {
      if (conditional->getInit() != nullptr ||
          conditional->getConditionVariable() != nullptr) {
        fail(conditional->getIfLoc(),
             "the supported C++ if statement cannot declare an initializer or condition variable");
        return std::nullopt;
      }
      // Clang has already instantiated this condition. A discarded constexpr
      // arm is not runtime behavior and must not add callees, loads, or
      // cleanup.
      if (conditional->isConstexpr()) {
        auto selected = conditional->getNondiscardedCase(context_);
        if (!selected) {
          fail(conditional->getIfLoc(),
               "dependent C++ if constexpr condition is unsupported");
          return std::nullopt;
        }
        const bool takes_then = *selected == conditional->getThen();
        auto branch =
            lower_branch(*selected, function,
                         allow_nested_scope ? CleanupScopeKind::Conditional
                                            : CleanupScopeKind::None);
        if (!branch)
          return std::nullopt;
        llvm::json::Object result;
        result["kind"] = "if";
        result["condition"] = boolean_constant(
            takes_then, conditional->getCond()->getSourceRange(), true);
        result["then_branch"] =
            takes_then ? std::move(*branch) : llvm::json::Array();
        result["else_branch"] =
            takes_then ? llvm::json::Array() : std::move(*branch);
        result["span"] = span(conditional->getSourceRange());
        return Json(std::move(result));
      }
      auto condition = lower_if_condition(conditional->getCond(), function);
      auto branch_scope = allow_nested_scope
                              ? CleanupScopeKind::Conditional
                              : CleanupScopeKind::None;
      auto then_branch =
          lower_branch(conditional->getThen(), function, branch_scope);
      auto else_branch =
          lower_branch(conditional->getElse(), function, branch_scope);
      if (!condition || !then_branch || !else_branch) {
        return std::nullopt;
      }
      llvm::json::Object result;
      result["kind"] = "if";
      result["condition"] = std::move(*condition);
      result["then_branch"] = std::move(*then_branch);
      result["else_branch"] = std::move(*else_branch);
      result["span"] = span(conditional->getSourceRange());
      return Json(std::move(result));
    }
    fail(statement->getBeginLoc(),
         "unsupported statement in the first C++ slice");
    return std::nullopt;
  }

  std::optional<Json> lower_call(const clang::CallExpr *call,
                                 const clang::FunctionDecl *caller) {
    auto lowered = lower_call_operation(call, caller, true);
    if (!lowered) {
      return std::nullopt;
    }
    llvm::json::Object result;
    result["kind"] = "call";
    result["callee"] = std::move(lowered->callee);
    result["arguments"] = std::move(lowered->arguments);
    result["span"] = std::move(lowered->span);
    return Json(std::move(result));
  }

  std::optional<Json>
  lower_try_catch_int32(const clang::CXXTryStmt *statement,
                        const clang::FunctionDecl *function) {
    if (statement->getNumHandlers() != 1) {
      fail(statement->getTryLoc(),
           "scalar int32 try/catch requires exactly one handler");
      return std::nullopt;
    }
    const clang::CXXCatchStmt *catch_statement = statement->getHandler(0);
    const clang::VarDecl *binding = catch_statement->getExceptionDecl();
    const auto *handler_block = llvm::dyn_cast<clang::CompoundStmt>(
        catch_statement->getHandlerBlock());
    if (binding == nullptr || binding->getName().empty() ||
        !context_.hasSameType(binding->getType(), context_.IntTy) ||
        handler_block == nullptr) {
      fail(catch_statement->getCatchLoc(),
           "scalar int32 handler requires one named by-value `int` binding");
      return std::nullopt;
    }
    if (!remember_local_declaration(function, binding)) {
      return std::nullopt;
    }
    auto binding_type =
        lower_type(binding->getType(), binding->getLocation(),
                   direct_source_alias(binding->getTypeSourceInfo()));
    if (!binding_type) {
      return std::nullopt;
    }

    // Preserve the source's conditional construction shape while making the
    // catch region explicit in the lowered C++ artifact.  The C++ source
    // permits the guard to be constructed only when the condition is true,
    // while the catch still encloses the potentially-throwing call.  Lowering
    // the conditional as an outer branch with the typed try/catch in its live
    // arm gives the C proof driver the real mixed outcome join: normal cleanup
    // reaches the branch continuation, while the caught path returns.
    if (statement->getTryBlock()->size() == 1) {
      const auto *conditional = llvm::dyn_cast<clang::IfStmt>(
          *statement->getTryBlock()->body_begin());
      if (conditional != nullptr && conditional->getInit() == nullptr &&
          conditional->getConditionVariable() == nullptr &&
          conditional->getElse() == nullptr) {
        const auto *live_scope =
            llvm::dyn_cast<clang::CompoundStmt>(conditional->getThen());
        const clang::DeclStmt *first_declaration =
            live_scope != nullptr && !live_scope->body_empty()
                ? llvm::dyn_cast<clang::DeclStmt>(*live_scope->body_begin())
                : nullptr;
        const clang::VarDecl *guard =
            first_declaration != nullptr && first_declaration->isSingleDecl()
                ? llvm::dyn_cast<clang::VarDecl>(
                      first_declaration->getSingleDecl())
                : nullptr;
        const auto *record_type =
            guard == nullptr ? nullptr
                             : guard->getType()->getAs<clang::RecordType>();
        const auto *record = record_type == nullptr
                                 ? nullptr
                                 : llvm::dyn_cast<clang::CXXRecordDecl>(
                                       record_type->getDecl()->getDefinition());
        const auto *destructor =
            record == nullptr ? nullptr : record->getDestructor();
        if (needs_destructor_body(destructor)) {
          // Moving an effectful predicate outside the catch would change
          // which handler catches its exception. Keep this shape pure.
          auto condition = lower_expression(conditional->getCond(), function);
          auto live_try_body = lower_branch(conditional->getThen(), function,
                                            CleanupScopeKind::Conditional);
          if (!condition || !live_try_body) {
            return std::nullopt;
          }
          active_catch_binding_ = binding;
          auto handler =
              lower_branch(handler_block, function, CleanupScopeKind::None);
          active_catch_binding_ = nullptr;
          if (!handler) {
            return std::nullopt;
          }

          llvm::json::Object nested_try;
          nested_try["kind"] = "try_catch_int32";
          nested_try["try_body"] = std::move(*live_try_body);
          llvm::json::Object nested_binding;
          nested_binding["declaration_id"] = declaration_id(binding);
          nested_binding["name"] = binding->getNameAsString();
          nested_binding["value_type"] = std::move(*binding_type);
          nested_binding["span"] = span(binding->getSourceRange());
          nested_try["binding"] = std::move(nested_binding);
          nested_try["handler"] = std::move(*handler);
          nested_try["span"] = span(statement->getSourceRange());

          llvm::json::Array then_branch;
          then_branch.push_back(std::move(nested_try));
          llvm::json::Array else_branch;
          llvm::json::Object result;
          result["kind"] = "if";
          result["condition"] = std::move(*condition);
          result["then_branch"] = std::move(then_branch);
          result["else_branch"] = std::move(else_branch);
          result["span"] = span(conditional->getSourceRange());
          return Json(std::move(result));
        }
      }
    }
    auto try_body =
        lower_branch(statement->getTryBlock(), function, CleanupScopeKind::Try);
    if (!binding_type || !try_body) {
      return std::nullopt;
    }
    active_catch_binding_ = binding;
    auto handler =
        lower_branch(handler_block, function, CleanupScopeKind::None);
    active_catch_binding_ = nullptr;
    if (!handler) {
      return std::nullopt;
    }
    llvm::json::Object place;
    place["declaration_id"] = declaration_id(binding);
    place["name"] = binding->getNameAsString();
    place["value_type"] = std::move(*binding_type);
    place["span"] = span(binding->getSourceRange());
    llvm::json::Object result;
    result["kind"] = "try_catch_int32";
    result["try_body"] = std::move(*try_body);
    result["binding"] = std::move(place);
    result["handler"] = std::move(*handler);
    result["span"] = span(statement->getSourceRange());
    return Json(std::move(result));
  }

  bool remember_local_declaration(const clang::FunctionDecl *function,
                                  const clang::VarDecl *local) {
    unsigned &count = local_declaration_counts_[function->getCanonicalDecl()];
    if (count == kMaxLocalDeclarations) {
      fail(local->getLocation(),
           "C++ artifact budget exhausted: local declarations per function (limit " +
               std::to_string(kMaxLocalDeclarations) + ")");
      return false;
    }
    ++count;
    return true;
  }

  struct ScalarCallSource {
    const clang::CallExpr *call;
    llvm::json::Array conversions;
  };

  // Preserve the resolved conversions around a whole call, without admitting
  // arbitrary effectful expressions. Initializers and returns share this path.
  std::optional<ScalarCallSource>
  lower_scalar_call_source(const clang::Expr *expression) {
    const clang::Expr *call_candidate = expression->IgnoreParens();
    llvm::json::Array call_conversions;
    std::vector<const clang::CastExpr *> casts;
    while (const auto *cast = llvm::dyn_cast<clang::CastExpr>(call_candidate)) {
      casts.push_back(cast);
      call_candidate = cast->getSubExpr()->IgnoreParens();
    }
    const auto *call = llvm::dyn_cast<clang::CallExpr>(call_candidate);
    const bool ordinary_call = call != nullptr && !is_numeric_limits_max_call(call) &&
        !(call->getDirectCallee() != nullptr &&
          call->getDirectCallee()->getBuiltinID() == clang::Builtin::BI__builtin_is_constant_evaluated);
    if (ordinary_call) {
      if (casts.size() > kMaxScalarConversions) {
        fail(expression->getExprLoc(),
             "C++ artifact budget exhausted: scalar call-result conversions (limit " +
                 std::to_string(kMaxScalarConversions) + ")");
        return std::nullopt;
      }
      for (auto it = casts.rbegin(); it != casts.rend(); ++it) {
        const clang::CastExpr *cast = *it;
        std::string kind;
        switch (cast->getCastKind()) {
        case clang::CK_NoOp:
          if (!context_.hasSameType(cast->getType(), cast->getSubExpr()->getType())) {
            fail(cast->getExprLoc(), "unsupported C++ call-result no-op conversion");
            return std::nullopt;
          }
          kind = "no_op";
          break;
        case clang::CK_BitCast:
          if (!supported_byte_pointer_cast(cast)) {
            fail(cast->getExprLoc(), "unsupported C++ call-result pointer reinterpretation");
            return std::nullopt;
          }
          kind = "byte_pointer_cast";
          break;
        case clang::CK_IntegralCast:
          kind = cast->getType()->isEnumeralType() ? "integral_to_enumeration" : "integral_cast";
          break;
        case clang::CK_IntegralToBoolean: kind = "integral_to_boolean"; break;
        case clang::CK_BooleanToSignedIntegral: kind = "boolean_to_signed_integral"; break;
        case clang::CK_LValueToRValue: {
          // Reading a returned native reference: only the call's own
          // result, before any other conversion, and never volatile.
          const auto *callee = call->getDirectCallee();
          const auto *reference = callee == nullptr
              ? nullptr
              : callee->getReturnType()->getAs<clang::LValueReferenceType>();
          if (it != casts.rbegin() || !call->isLValue() || reference == nullptr ||
              !supported_pointer_element(reference->getPointeeType())) {
            fail(cast->getExprLoc(), "unsupported C++ call-result conversion");
            return std::nullopt;
          }
          kind = "reference_load";
          break;
        }
        default:
          fail(cast->getExprLoc(), "unsupported C++ call-result conversion");
          return std::nullopt;
        }
        auto source_alias = [this](const clang::Expr *value) {
          value = value->IgnoreParens();
          if (const auto *explicit_cast = llvm::dyn_cast<clang::ExplicitCastExpr>(value))
            return direct_source_alias(explicit_cast->getTypeInfoAsWritten());
          if (const auto *call = llvm::dyn_cast<clang::CallExpr>(value);
              call != nullptr && call->getDirectCallee() != nullptr)
            return direct_source_alias(call->getDirectCallee()->getTypeSourceInfo());
          return static_cast<const clang::TypedefNameDecl *>(nullptr);
        };
        auto source_type = kind == "reference_load"
            ? lower_type(call->getDirectCallee()->getReturnType(), cast->getExprLoc())
            : lower_type(cast->getSubExpr()->getType().getUnqualifiedType(), cast->getExprLoc(),
                         source_alias(cast->getSubExpr()));
        auto value_type = lower_type(cast->getType().getUnqualifiedType(), cast->getExprLoc(), source_alias(cast));
        if (!source_type || !value_type) return std::nullopt;
        llvm::json::Object conversion;
        conversion["cast_kind"] = kind;
        conversion["explicit"] = llvm::isa<clang::ExplicitCastExpr>(cast);
        conversion["source_type"] = std::move(*source_type);
        conversion["value_type"] = std::move(*value_type);
        conversion["span"] = span(cast->getSourceRange());
        call_conversions.push_back(std::move(conversion));
      }
    }
    return ScalarCallSource{
        ordinary_call ? call : nullptr,
        std::move(call_conversions)};
  }

  std::optional<Json>
  lower_local_declaration(const clang::DeclStmt *statement,
                          const clang::FunctionDecl *function,
                          bool function_body_local) {
    if (!statement->isSingleDecl()) {
      fail(statement->getBeginLoc(),
           "the supported C++ local declaration must declare exactly one variable");
      return std::nullopt;
    }
    const auto *local =
        llvm::dyn_cast<clang::VarDecl>(statement->getSingleDecl());
    if (local == nullptr || !local->hasLocalStorage() || local->isStaticLocal()) {
      fail(statement->getBeginLoc(),
           "the supported C++ local must have automatic storage");
      return std::nullopt;
    }
    if (!remember_local_declaration(function, local)) {
      return std::nullopt;
    }
    // A local of a generic template's abstract type argument holds a value
    // of it, as an integer local holds an integer.
    const bool archetype_value =
        archetype_name(local->getType().getUnqualifiedType()) != nullptr;
    const bool scalar_int = (supported_scalar_value_type(local->getType().getUnqualifiedType()) ||
                             archetype_value) &&
        !local->getType().isVolatileQualified() && !local->getType().isRestrictQualified();
    const bool mutable_int = scalar_int && !local->getType().isConstQualified();
    const auto *local_pointer = local->getType()->getAs<clang::PointerType>();
    const auto *pointed_record = record_pointer_target(local->getType());
    const bool mutable_pointer = (local_pointer && !local->getType().hasQualifiers() &&
        !local_pointer->getPointeeType().hasQualifiers() && supported_pointer_element(local_pointer->getPointeeType())) ||
        pointed_record != nullptr;
    if (pointed_record != nullptr && !remember_record(pointed_record)) {
      return std::nullopt;
    }
    const auto *local_reference = local->getType()->getAs<clang::LValueReferenceType>();
    const bool int_reference = local_reference != nullptr &&
        supported_pointer_element(local_reference->getPointeeType());
    const auto *record_type = local->getType()->getAs<clang::RecordType>();
    const auto *record =
        record_type == nullptr
            ? nullptr
            : llvm::dyn_cast<clang::CXXRecordDecl>(
                  record_type->getDecl()->getDefinition());
    const bool record_object =
        record != nullptr && !archetype_value && !local->getType().hasQualifiers();
    // A function-pointer local holds `&f` or another pointer's value; calls
    // through it are lowered as calls through a parameter are.
    const bool function_pointer_local =
        function_pointer_prototype(local->getType()) != nullptr &&
        !local->getType().hasQualifiers();
    if (record_object && loop_depth_ != 0) {
      fail(local->getLocation(),
           "a C++ loop body declares only scalar and pointer locals");
      return std::nullopt;
    }
    if (record_object && context_.getLangOpts().CXXExceptions &&
        exception_behavior_ == "normal_only" && !record->hasTrivialDestructor()) {
      fail(local->getLocation(),
           "exception-enabled normal-only C++ local objects require trivial destruction");
      return std::nullopt;
    }
    if (!scalar_int && !mutable_pointer && !record_object && !int_reference &&
        !function_pointer_local) {
      fail(local->getLocation(),
           "the supported automatic C++ local must resolve to "
           "signed/unsigned "
           "32/64/128-bit integer or unsigned char, an initialized native object or simple record pointer, a native element lvalue reference, a function pointer, or one simple record object");
      return std::nullopt;
    }
    if (!local->hasInit() && !mutable_int) {
      fail(local->getLocation(),
           record_object
               ? "a supported C++ record local requires direct aggregate or constructor initialization"
               : "the supported automatic C++ local requires an initializer");
      return std::nullopt;
    }
    if (record_object) {
      const clang::FunctionDecl *canonical = function->getCanonicalDecl();
      if (!remember_record(record)) {
        return std::nullopt;
      }
      const clang::CXXDestructorDecl *destructor = record->getDestructor();
      const bool destructible = needs_destructor_body(destructor);
      if (function_body_local) {
        if (functions_with_nested_scope_.contains(canonical)) {
          fail(local->getLocation(),
               "nested-scope cleanup cannot yet be combined with an outer aggregate object");
          return std::nullopt;
        }
        if (!functions_with_aggregate_local_.insert(canonical).second) {
          const auto previous = cleanup_locals_.find(canonical);
          if (!destructible || previous == cleanup_locals_.end() ||
              previous->second.empty()) {
            fail(local->getLocation(),
                 "the supported C++ slice permits multiple aggregate objects only when all require destruction");
            return std::nullopt;
          }
        }
      }
      if (destructible) {
        const auto *definition =
            llvm::dyn_cast_or_null<clang::CXXDestructorDecl>(
                destructor->getDefinition());
        if (definition == nullptr ||
            (function_body_local &&
             !validate_return_cleanup_source(function, local))) {
          if (definition == nullptr && state_.error.empty()) {
            fail(destructor->getLocation(),
                 "the supported destructor has no reachable definition");
          }
          return std::nullopt;
        }
        cleanup_locals_[canonical].push_back(local);
        if (!remember_function(definition)) {
          return std::nullopt;
        }
      }
    }

    auto value_type = lower_type(local->getType(), local->getLocation());
    if (!value_type) {
      return std::nullopt;
    }
    llvm::json::Object place;
    place["declaration_id"] = declaration_id(local);
    place["name"] = local->getNameAsString();
    place["value_type"] = std::move(*value_type);
    place["span"] = span(local->getSourceRange());

    if (!local->hasInit()) {
      llvm::json::Object initializer;
      initializer["kind"] = "uninitialized";
      llvm::json::Object result;
      result["kind"] = "declare";
      result["local"] = std::move(place);
      result["initializer"] = std::move(initializer);
      result["span"] = span(statement->getSourceRange());
      return Json(std::move(result));
    }

    llvm::json::Object initializer;
    const clang::Expr *source_initializer = local->getInit();
    const clang::Expr *semantic_initializer =
        source_initializer->IgnoreParenImpCasts();
    auto scalar_call = lower_scalar_call_source(source_initializer);
    if (!scalar_call) return std::nullopt;
    const auto *initializer_call = scalar_call->call;
    if (record_object && initializer_call != nullptr && initializer_call->isPRValue() &&
        context_.hasSameUnqualifiedType(initializer_call->getType(), local->getType())) {
      if (!record->isTriviallyCopyable() || !record->hasTrivialDestructor() || !scalar_call->conversions.empty()) {
        fail(source_initializer->getExprLoc(), "C++ construction-call locals require trivial records and no conversion");
        return std::nullopt;
      }
      auto operation = lower_call_operation(initializer_call, function, true);
      if (!operation) return std::nullopt;
      initializer["kind"] = "construction_call";
      initializer["callee"] = std::move(operation->callee);
      initializer["arguments"] = std::move(operation->arguments);
      initializer["span"] = span(source_initializer->getSourceRange());
    } else if (record_object &&
               member_initialized_default_construction(source_initializer, record)) {
      // The implicit default constructor runs each default member
      // initializer in declaration order and nothing else.
      if (!remember_record(record)) return std::nullopt;
      llvm::json::Array fields;
      for (const clang::FieldDecl *field : record->fields()) {
        const clang::Expr *member_initializer = field->getInClassInitializer();
        auto value = lower_expression(member_initializer, function);
        if (!value) return std::nullopt;
        llvm::json::Object field_reference;
        field_reference["record_declaration_id"] = declaration_id(record);
        field_reference["declaration_id"] = declaration_id(field);
        field_reference["name"] = field->getNameAsString();
        field_reference["span"] = span(field->getSourceRange());
        llvm::json::Object field_initializer;
        field_initializer["field"] = std::move(field_reference);
        field_initializer["value"] = std::move(*value);
        field_initializer["span"] = span(member_initializer->getSourceRange());
        fields.push_back(std::move(field_initializer));
      }
      initializer["kind"] = "aggregate";
      initializer["fields"] = std::move(fields);
      initializer["span"] = span(source_initializer->getSourceRange());
    } else if (record_object && record->isAggregate()) {
      const auto *semantic_list =
          llvm::dyn_cast<clang::InitListExpr>(source_initializer);
      const clang::InitListExpr *syntactic_list = semantic_list;
      if (semantic_list != nullptr && semantic_list->getSyntacticForm() != nullptr) {
        syntactic_list = semantic_list->getSyntacticForm();
      }
      const unsigned field_count = std::distance(record->field_begin(),
                                                 record->field_end());
      if (has_stateless_field(record)) {
        fail(source_initializer->getExprLoc(),
             "supported C++ aggregate locals require records without stateless members");
        return std::nullopt;
      }
      if (local->getInitStyle() != clang::VarDecl::ListInit ||
          syntactic_list == nullptr || syntactic_list->getNumInits() != field_count) {
        fail(source_initializer->getExprLoc(),
             "a supported C++ aggregate local requires one direct brace initializer per field in declaration order");
        return std::nullopt;
      }
      llvm::json::Array fields;
      unsigned index = 0;
      for (const clang::FieldDecl *field : record->fields()) {
        const clang::Expr *field_source = syntactic_list->getInit(index++);
        const clang::Expr *field_semantic =
            semantic_list->getInit(index - 1);
        auto value = lower_expression(field_semantic, function);
        if (!value) {
          return std::nullopt;
        }
        llvm::json::Object field_reference;
        field_reference["record_declaration_id"] = declaration_id(record);
        field_reference["declaration_id"] = declaration_id(field);
        field_reference["name"] = field->getNameAsString();
        field_reference["span"] = span(field->getSourceRange());
        llvm::json::Object field_initializer;
        field_initializer["field"] = std::move(field_reference);
        field_initializer["value"] = std::move(*value);
        field_initializer["span"] = span(field_source->getSourceRange());
        fields.push_back(std::move(field_initializer));
      }
      initializer["kind"] = "aggregate";
      initializer["fields"] = std::move(fields);
      initializer["span"] = span(source_initializer->getSourceRange());
    } else if (record_object) {
      const auto *construction =
          llvm::dyn_cast<clang::CXXConstructExpr>(semantic_initializer);
      const clang::CXXConstructorDecl *constructor =
          construction == nullptr ? nullptr : construction->getConstructor();
      const auto *definition = constructor == nullptr
                                   ? nullptr
                                   : llvm::dyn_cast_or_null<clang::CXXConstructorDecl>(
                                         constructor->getDefinition());
      if (local->getInitStyle() != clang::VarDecl::CallInit ||
          construction == nullptr || definition == nullptr ||
          construction->getConstructionKind() != clang::CXXConstructionKind::Complete ||
          definition->getParent()->getCanonicalDecl() !=
              record->getCanonicalDecl() ||
          construction->getNumArgs() != definition->getNumParams()) {
        fail(source_initializer->getExprLoc(),
             "a supported C++ object local requires one direct parenthesized call to its explicit constructor");
        return std::nullopt;
      }
      llvm::json::Array arguments;
      for (unsigned index = 0; index < construction->getNumArgs(); ++index) {
        auto argument = lower_call_argument(construction->getArg(index),
                                            definition->getParamDecl(index),
                                            function);
        if (!argument) {
          return std::nullopt;
        }
        arguments.push_back(std::move(*argument));
      }
      if (!remember_function(definition)) {
        return std::nullopt;
      }
      llvm::json::Object reference;
      reference["declaration_id"] = declaration_id(definition);
      reference["name"] = constructor_name(definition);
      reference["span"] = span(source_initializer->getSourceRange());
      initializer["kind"] = "constructor";
      initializer["callee"] = std::move(reference);
      initializer["arguments"] = std::move(arguments);
      initializer["span"] = span(source_initializer->getSourceRange());
    } else if (const auto *call = initializer_call;
               call != nullptr && !is_numeric_limits_max_call(call)) {
      if (!(int_reference
              ? source_initializer->isLValue() && scalar_call->conversions.empty() &&
                context_.hasSameType(call->getCallReturnType(context_), local->getType())
              : context_.hasSameType(source_initializer->getType().getUnqualifiedType(), local->getType().getUnqualifiedType()))) {
        fail(call->getExprLoc(),
             "C++ call capture requires matching final initializer and local types");
        return std::nullopt;
      }
      auto lowered = lower_call_operation(call, function, true);
      if (!lowered) {
        return std::nullopt;
      }
      initializer["kind"] = "call";
      if (!scalar_call->conversions.empty())
        initializer["conversions"] = std::move(scalar_call->conversions);
      initializer["callee"] = std::move(lowered->callee);
      initializer["arguments"] = std::move(lowered->arguments);
      initializer["span"] = std::move(lowered->span);
    } else {
      auto value = int_reference
          ? lower_reference_binding(source_initializer, local->getType(), function)
          : lower_expression(source_initializer, function);
      if (!value) {
        return std::nullopt;
      }
      initializer["kind"] = "value";
      initializer["value"] = std::move(*value);
    }

    llvm::json::Object result;
    result["kind"] = "declare";
    result["local"] = std::move(place);
    result["initializer"] = std::move(initializer);
    result["span"] = span(statement->getSourceRange());
    if (!state_.error.empty()) {
      return std::nullopt;
    }
    return Json(std::move(result));
  }

  std::optional<Json> lower_scope(const clang::CompoundStmt *scope,
                                  const clang::FunctionDecl *function,
                                  bool conditional_arm) {
    const clang::FunctionDecl *canonical = function->getCanonicalDecl();
    auto &active = cleanup_locals_[canonical];
    const bool has_outer_aggregate =
        functions_with_aggregate_local_.contains(canonical);
    unsigned &scope_count = nested_scope_counts_[canonical];
    if (llvm::isa<clang::CXXMethodDecl>(function)) {
      fail(scope->getLBracLoc(),
           "nested C++ scopes are supported only in a free-function body");
      return std::nullopt;
    }
    if (conditional_arm && (has_outer_aggregate || !active.empty())) {
      fail(scope->getLBracLoc(),
           "conditional construction cannot yet be combined with an outer aggregate object");
      return std::nullopt;
    }
    if (conditional_arm && scope_count != 0) {
      fail(scope->getLBracLoc(),
           "the conditional-construction slice permits exactly one cleanup scope in one if arm");
      return std::nullopt;
    }
    if (!conditional_arm &&
        functions_with_conditional_scope_.contains(canonical)) {
      fail(scope->getLBracLoc(),
           "the conditional-construction slice cannot be combined with another cleanup scope");
      return std::nullopt;
    }
    if (has_outer_aggregate && active.size() != 1) {
      fail(scope->getLBracLoc(),
           "the overlapping cleanup-scope slice requires exactly one outer destructible object");
      return std::nullopt;
    }
    if (has_outer_aggregate && scope_count != 0) {
      fail(scope->getLBracLoc(),
           "the overlapping cleanup-scope slice permits one inner cleanup scope with an outer object");
      return std::nullopt;
    }
    if (!has_outer_aggregate && !active.empty()) {
      fail(scope->getLBracLoc(),
           "nested-scope cleanup cannot yet be combined with an unsupported outer destructible object");
      return std::nullopt;
    }
    if (scope_count == kMaxCleanupScopes) {
      fail(scope->getLBracLoc(),
           "C++ artifact budget exhausted: cleanup scopes per function (limit " +
               std::to_string(kMaxCleanupScopes) + ")");
      return std::nullopt;
    }
    functions_with_nested_scope_.insert(canonical);
    if (conditional_arm) {
      functions_with_conditional_scope_.insert(canonical);
    }
    ++scope_count;
    const std::size_t entry_count = active.size();
    unsigned local_count = 0;
    llvm::json::Array body;
    for (const clang::Stmt *statement : scope->body()) {
      if (is_checked_runtime_noop(statement)) continue;
      if (llvm::isa<clang::DeclStmt>(statement)) {
        ++local_count;
      }
      auto lowered = lower_statement(statement, function, true, false);
      if (!lowered) {
        return std::nullopt;
      }
      body.push_back(std::move(*lowered));
    }
    const std::size_t new_count =
        active.size() < entry_count ? 0 : active.size() - entry_count;
    if (local_count != new_count || new_count == 0) {
      fail(scope->getLBracLoc(),
           "the nested-scope slice requires destructible objects and no other locals");
      return std::nullopt;
    }
    llvm::json::Array cleanups;
    for (std::size_t index = 0; index < new_count; ++index) {
      auto cleanup = lower_cleanup(active[active.size() - 1 - index],
                                   scope->getSourceRange());
      if (!cleanup) {
        return std::nullopt;
      }
      cleanups.push_back(std::move(*cleanup));
    }
    active.resize(entry_count);

    llvm::json::Object result;
    result["kind"] = "scope";
    result["body"] = std::move(body);
    result["cleanups"] = std::move(cleanups);
    result["span"] = span(scope->getSourceRange());
    return Json(std::move(result));
  }

  std::optional<Json> lower_cleanup(const clang::VarDecl *local,
                                    clang::SourceRange edge) {
    const auto *record_type = local->getType()->getAs<clang::RecordType>();
    const auto *record =
        record_type == nullptr
            ? nullptr
            : llvm::dyn_cast<clang::CXXRecordDecl>(
                  record_type->getDecl()->getDefinition());
    const clang::CXXDestructorDecl *destructor =
        record == nullptr ? nullptr : record->getDestructor();
    const auto *definition =
        destructor == nullptr
            ? nullptr
            : llvm::dyn_cast_or_null<clang::CXXDestructorDecl>(
                  destructor->getDefinition());
    if (record == nullptr || definition == nullptr) {
      fail(edge.getBegin(),
           "could not resolve the automatic object's destructor at the cleanup edge");
      return std::nullopt;
    }
    llvm::json::Object object;
    object["declaration_id"] = declaration_id(local);
    object["name"] = local->getNameAsString();
    object["span"] = span(local->getSourceRange());
    llvm::json::Object callee;
    callee["declaration_id"] = declaration_id(definition);
    callee["name"] = destructor_name(definition);
    callee["span"] = span(definition->getNameInfo().getSourceRange());
    llvm::json::Object cleanup_call;
    cleanup_call["kind"] = "destructor";
    cleanup_call["object"] = std::move(object);
    cleanup_call["callee"] = std::move(callee);
    cleanup_call["span"] = span(edge);
    return Json(std::move(cleanup_call));
  }

  bool validate_return_cleanup_source(const clang::FunctionDecl *function,
                                      const clang::VarDecl *local) {
    const auto *body =
        llvm::dyn_cast_or_null<clang::CompoundStmt>(function->getBody());
    if (body == nullptr || body->body_empty() ||
        !llvm::isa<clang::ReturnStmt>(body->body_back())) {
      fail(local->getLocation(),
           "the return-cleanup slice requires one final return after object construction");
      return false;
    }
    return true;
  }

  const clang::Expr *
  scalar_list_initializer(const clang::InitListExpr *list) const {
    const auto *syntax = list->getSyntacticForm();
    if (syntax == nullptr)
      syntax = list;
    const auto type = list->getType();
    if (!list->isSemanticForm() || !type->isIntegerType() ||
        (!type->isBooleanType() && !supported_integer_type(type)) ||
        list->getNumInits() != 1 || syntax->getNumInits() != 1 ||
        !context_.hasSameUnqualifiedType(type, list->getInit(0)->getType()))
      return nullptr;
    return list->getInit(0);
  }

  bool stable_scalar_argument(const clang::Expr *expression,
                              const clang::FunctionDecl *caller) const {
    expression = expression->IgnoreParens();
    if (const auto *substitution =
            llvm::dyn_cast<clang::SubstNonTypeTemplateParmExpr>(expression))
      return stable_scalar_argument(substitution->getReplacement(), caller);
    if (const auto *cast = llvm::dyn_cast<clang::CastExpr>(expression)) {
      switch (cast->getCastKind()) {
      case clang::CK_LValueToRValue:
      case clang::CK_IntegralCast:
      case clang::CK_IntegralToBoolean:
      case clang::CK_NoOp:
        return stable_scalar_argument(cast->getSubExpr(), caller);
      default:
        return false;
      }
    }
    if (const auto *list = llvm::dyn_cast<clang::InitListExpr>(expression)) {
      const auto *value = scalar_list_initializer(list);
      return value != nullptr && stable_scalar_argument(value, caller);
    }
    if (llvm::isa<clang::IntegerLiteral>(expression) ||
        llvm::isa<clang::CXXBoolLiteralExpr>(expression) ||
        llvm::isa<clang::UnaryExprOrTypeTraitExpr>(expression))
      return true;
    if (const auto *call = llvm::dyn_cast<clang::CallExpr>(expression))
      return is_numeric_limits_max_call(call);
    if (const auto *reference =
            llvm::dyn_cast<clang::DeclRefExpr>(expression)) {
      const auto *variable =
          llvm::dyn_cast<clang::VarDecl>(reference->getDecl());
      return variable != nullptr && variable->getType()->isIntegerType() &&
             !variable->getType().isVolatileQualified() &&
             (variable->isConstexpr() ||
              (variable->getDeclContext() == caller &&
               (llvm::isa<clang::ParmVarDecl>(variable) ||
                (variable->hasLocalStorage() && !variable->isStaticLocal()))));
    }
    return false;
  }

  bool scalar_only_call(const clang::CallExpr *call) const {
    const auto *callee = call->getDirectCallee();
    if (callee == nullptr) return false;
    const auto *method = llvm::dyn_cast<clang::CXXMethodDecl>(callee);
    if (method != nullptr && !method->isStatic()) return false;
    for (const auto *parameter : callee->parameters())
      if (!parameter->getType()->isIntegerType()) return false;
    for (const auto *argument : call->arguments()) {
      if (!argument->getType()->isIntegerType()) return false;
      if (const auto *nested = llvm::dyn_cast<clang::CallExpr>(argument->IgnoreParens()))
        if (!is_numeric_limits_max_call(nested)) return false;
    }
    return true;
  }

  bool field_scalar_argument(const clang::Expr *expression) const {
    expression = expression->IgnoreParens();
    if (const auto *cast = llvm::dyn_cast<clang::CastExpr>(expression)) {
      switch (cast->getCastKind()) {
      case clang::CK_LValueToRValue:
      case clang::CK_IntegralCast:
      case clang::CK_IntegralToBoolean:
      case clang::CK_NoOp:
        return field_scalar_argument(cast->getSubExpr());
      default: return false;
      }
    }
    if (const auto *list = llvm::dyn_cast<clang::InitListExpr>(expression)) {
      const auto *value = scalar_list_initializer(list);
      return value != nullptr && field_scalar_argument(value);
    }
    return llvm::isa<clang::MemberExpr>(expression) &&
           expression->getType()->isIntegerType() &&
           !expression->getType().isVolatileQualified();
  }

  // Evaluated library assertions may read supported fields; the unevaluated
  // builtin must remain total without memory reads. Both reject calls, effects
  // and partial arithmetic. Ordinary expression lowering checks field places.
  bool checked_boolean_condition(const clang::Expr *expression,
                                  const clang::FunctionDecl *caller, bool field_reads) const {
    expression = expression->IgnoreParens();
    if (const auto *cast = llvm::dyn_cast<clang::CastExpr>(expression)) {
      if (cast->getCastKind() == clang::CK_IntegralToBoolean ||
          cast->getCastKind() == clang::CK_NoOp)
        return checked_boolean_condition(cast->getSubExpr(), caller, field_reads);
    }
    if (const auto *list = llvm::dyn_cast<clang::InitListExpr>(expression)) {
      const auto *value = scalar_list_initializer(list);
      return value != nullptr && checked_boolean_condition(value, caller, field_reads);
    }
    if (const auto *unary = llvm::dyn_cast<clang::UnaryOperator>(expression);
        unary != nullptr && unary->getOpcode() == clang::UO_LNot)
      return checked_boolean_condition(unary->getSubExpr(), caller, field_reads);
    if (const auto *binary = llvm::dyn_cast<clang::BinaryOperator>(expression)) {
      if (binary->getOpcode() == clang::BO_LAnd)
        return checked_boolean_condition(binary->getLHS(), caller, field_reads) &&
               checked_boolean_condition(binary->getRHS(), caller, field_reads);
      if (binary->isComparisonOp())
        return (stable_scalar_argument(binary->getLHS(), caller) ||
                (field_reads && field_scalar_argument(binary->getLHS()))) &&
               (stable_scalar_argument(binary->getRHS(), caller) ||
                (field_reads && field_scalar_argument(binary->getRHS())));
      return false;
    }
    return stable_scalar_argument(expression, caller) ||
           (field_reads && field_scalar_argument(expression));
  }

  std::optional<Json> lower_if_condition(const clang::Expr *expression,
                                        const clang::FunctionDecl *function) {
    const auto *call = llvm::dyn_cast<clang::CallExpr>(expression->IgnoreParens());
    if (call == nullptr || (call->getDirectCallee() != nullptr &&
        call->getDirectCallee()->getBuiltinID() == clang::Builtin::BI__builtin_is_constant_evaluated))
      return lower_expression(expression, function);
    if (!call->getType()->isBooleanType()) {
      fail(call->getExprLoc(), "C++ condition calls require a Boolean result");
      return std::nullopt;
    }
    auto operation = lower_call_operation(call, function, true);
    auto value_type = lower_type(call->getType(), call->getExprLoc());
    if (!operation || !value_type)
      return std::nullopt;
    llvm::json::Object predicate;
    predicate["callee"] = std::move(operation->callee);
    predicate["arguments"] = std::move(operation->arguments);
    predicate["value_type"] = std::move(*value_type);
    predicate["span"] = std::move(operation->span);
    llvm::json::Object condition;
    condition["call"] = std::move(predicate);
    return Json(std::move(condition));
  }

  // A call through a function-pointer parameter or local, `f(x)` or
  // `(*f)(x)`. The callee is the variable; the contract its value meets
  // comes from the sidecar, as for a C callback. Its arguments are values,
  // never nested calls, so evaluation order needs no further evidence.
  // `f(x)` on a `std::function` parameter or local is a call through the
  // callable value it holds, as through a function pointer.
  std::optional<LoweredCall>
  lower_std_function_call(const clang::CXXOperatorCallExpr *call,
                          const clang::FunctionDecl *caller) {
    const auto *reference =
        llvm::dyn_cast<clang::DeclRefExpr>(call->getArg(0)->IgnoreParenImpCasts());
    const auto *variable =
        reference == nullptr ? nullptr : llvm::dyn_cast<clang::VarDecl>(reference->getDecl());
    const auto *prototype =
        variable == nullptr ? nullptr : std_function_prototype(variable->getType());
    if (variable == nullptr || !variable->hasLocalStorage() || prototype == nullptr) {
      fail(call->getExprLoc(),
           "the supported C++ slice calls a std::function parameter or local");
      return std::nullopt;
    }
    if (!lower_type(variable->getType(), variable->getLocation()))
      return std::nullopt;
    if (call->getNumArgs() != prototype->getNumParams() + 1) {
      fail(call->getExprLoc(),
           "the supported C++ slice requires a call with one argument per parameter");
      return std::nullopt;
    }
    llvm::json::Array arguments;
    for (unsigned index = 1; index < call->getNumArgs(); ++index) {
      const auto *argument = call->getArg(index);
      if (llvm::isa<clang::CallExpr>(argument->IgnoreParenImpCasts())) {
        fail(argument->getExprLoc(),
             "a call through a std::function takes no call as an argument");
        return std::nullopt;
      }
      auto lowered = lower_call_argument(argument, prototype->getParamType(index - 1),
                                         argument->getExprLoc(), caller);
      if (!lowered)
        return std::nullopt;
      arguments.push_back(std::move(*lowered));
    }
    llvm::json::Object callee;
    callee["declaration_id"] = declaration_id(variable);
    callee["name"] = variable->getNameAsString();
    callee["span"] = span(call->getArg(0)->getSourceRange());
    callee["through_pointer"] = true;
    Json call_span = span(call->getSourceRange());
    if (!state_.error.empty())
      return std::nullopt;
    return LoweredCall{std::move(callee), std::move(arguments), std::move(call_span)};
  }

  std::optional<LoweredCall>
  lower_indirect_call(const clang::CallExpr *call,
                      const clang::FunctionDecl *caller) {
    const clang::Expr *target = call->getCallee()->IgnoreParenImpCasts();
    if (const auto *dereference = llvm::dyn_cast<clang::UnaryOperator>(target);
        dereference != nullptr && dereference->getOpcode() == clang::UO_Deref)
      target = dereference->getSubExpr()->IgnoreParenImpCasts();
    const auto *reference = llvm::dyn_cast<clang::DeclRefExpr>(target);
    const auto *variable =
        reference == nullptr ? nullptr : llvm::dyn_cast<clang::VarDecl>(reference->getDecl());
    if (variable == nullptr || !variable->hasLocalStorage() ||
        function_pointer_prototype(variable->getType()) == nullptr) {
      fail(call->getExprLoc(),
           "the supported C++ slice calls a function directly or through a "
           "function-pointer parameter or local");
      return std::nullopt;
    }
    const auto *prototype = function_pointer_prototype(variable->getType());
    if (!lower_type(variable->getType(), variable->getLocation()))
      return std::nullopt;
    if (call->getNumArgs() != prototype->getNumParams()) {
      fail(call->getExprLoc(),
           "the supported C++ slice requires a call with one argument per parameter");
      return std::nullopt;
    }
    llvm::json::Array arguments;
    for (unsigned index = 0; index < call->getNumArgs(); ++index) {
      const auto *argument = call->getArg(index);
      if (llvm::isa<clang::CallExpr>(argument->IgnoreParenImpCasts())) {
        fail(argument->getExprLoc(),
             "a call through a function pointer takes no call as an argument");
        return std::nullopt;
      }
      auto lowered = lower_call_argument(argument, prototype->getParamType(index),
                                         argument->getExprLoc(), caller);
      if (!lowered)
        return std::nullopt;
      arguments.push_back(std::move(*lowered));
    }
    llvm::json::Object callee;
    callee["declaration_id"] = declaration_id(variable);
    callee["name"] = variable->getNameAsString();
    callee["span"] = span(call->getCallee()->getSourceRange());
    callee["through_pointer"] = true;
    Json call_span = span(call->getSourceRange());
    if (!state_.error.empty())
      return std::nullopt;
    return LoweredCall{std::move(callee), std::move(arguments),
                       std::move(call_span)};
  }

  std::optional<LoweredCall>
  lower_call_operation(const clang::CallExpr *call,
                       const clang::FunctionDecl *caller,
                       bool allow_nested = false) {
    const clang::FunctionDecl *callee = call->getDirectCallee();
    // A value of an abstract type argument is passed only to a method of a
    // template at abstract arguments, which is that template's method at
    // every type: any other function could be another overload, or another
    // template's specialization, at each type.
    for (const clang::Expr *argument : call->arguments())
      if (mentions_archetype(argument->getType()) &&
          (callee == nullptr || !is_generic_body(callee))) {
        fail(argument->getExprLoc(),
             "a value of an abstract type argument is passed only to the "
             "template's own methods");
        return std::nullopt;
      }
    if (callee == nullptr)
      return lower_indirect_call(call, caller);
    if (const auto *operation = llvm::dyn_cast<clang::CXXOperatorCallExpr>(call);
        operation != nullptr && operation->getOperator() == clang::OO_Call &&
        operation->getNumArgs() > 0 &&
        std_function_prototype(operation->getArg(0)->getType()) != nullptr)
      return lower_std_function_call(operation, caller);
    const auto *method = llvm::dyn_cast<clang::CXXMethodDecl>(callee);
    const clang::Expr *receiver = nullptr;
    unsigned argument_offset = 0;
    if (method != nullptr && method->isStatic() &&
        !llvm::isa<clang::DeclRefExpr>(
            call->getCallee()->IgnoreParenImpCasts())) {
      fail(call->getExprLoc(),
           "static C++ calls require class-qualified or unqualified dispatch");
      return std::nullopt;
    }
    const bool has_receiver = method != nullptr && !method->isStatic();
    // A virtual call names the method of the receiver's static type; it is
    // checked against that method's contract, which every override of it
    // refines. A qualified call, `shape.Shape::area()`, does not dispatch.
    bool qualified = false;
    if (const auto *member = llvm::dyn_cast<clang::MemberExpr>(
            call->getCallee()->IgnoreParenImpCasts()))
      qualified = member->hasQualifier();
    if (has_receiver) {
      if (llvm::isa<clang::CXXConstructorDecl>(method) ||
          llvm::isa<clang::CXXDestructorDecl>(method) ||
          (method->isPureVirtual() && qualified)) {
        fail(call->getExprLoc(), "unsupported C++ method dispatch");
        return std::nullopt;
      }
      if (const auto *member_call =
              llvm::dyn_cast<clang::CXXMemberCallExpr>(call)) {
        receiver = member_call->getImplicitObjectArgument();
      } else if (const auto *operator_call =
                     llvm::dyn_cast<clang::CXXOperatorCallExpr>(call)) {
        if (operator_call->getNumArgs() == 0)
          return std::nullopt;
        receiver = operator_call->getArg(0);
        argument_offset = 1;
      }
      if (receiver == nullptr ||
          (receiver->getType()->isPointerType() &&
           !llvm::isa<clang::CXXThisExpr>(receiver->IgnoreParenImpCasts()))) {
        fail(call->getExprLoc(), "supported C++ method call requires a direct "
                                 "record lvalue receiver");
        return std::nullopt;
      }
    }
    const clang::FunctionDecl *definition = callee->getDefinition();
    if (definition == nullptr && is_axiom(callee))
      definition = callee;
    if (method != nullptr && method->isPureVirtual())
      definition = method->getCanonicalDecl();
    if (definition == nullptr) {
      fail(call->getExprLoc(),
           "direct C++ call has no reachable function definition");
      return std::nullopt;
    }
    const clang::SourceLocation definition_location =
        source_manager_.getSpellingLoc(definition->getLocation());
    if (!is_axiom(definition) && !executable_source(definition_location)) {
      fail(call->getExprLoc(),
           "the supported C++ call graph requires definitions in selected or dependency sources");
      return std::nullopt;
    }
    if (call->getNumArgs() != definition->getNumParams() + argument_offset) {
      fail(call->getExprLoc(),
           "the supported C++ slice requires a call with one argument per parameter");
      return std::nullopt;
    }

    if (allow_nested) {
      unsigned nested_calls = 0;
      for (unsigned index = argument_offset; index < call->getNumArgs();
           ++index) {
        const auto *nested = llvm::dyn_cast<clang::CallExpr>(
            call->getArg(index)->IgnoreParens());
        if (nested != nullptr && nested->getDirectCallee() == nullptr) {
          fail(nested->getExprLoc(),
               "a call through a function pointer is not admitted as a call argument");
          return std::nullopt;
        }
        if (nested != nullptr && !is_numeric_limits_max_call(nested))
          ++nested_calls;
      }
      if (nested_calls > 1 || (nested_calls != 0 && has_receiver)) {
        fail(call->getExprLoc(),
             "nested C++ call arguments require one call and order-independent scalar "
             "siblings to preserve evaluation order");
        return std::nullopt;
      }
      if (nested_calls == 1) {
        bool isolated = false;
        for (unsigned index = argument_offset; index < call->getNumArgs(); ++index) {
          const auto *nested = llvm::dyn_cast<clang::CallExpr>(call->getArg(index)->IgnoreParens());
          if (nested != nullptr && !is_numeric_limits_max_call(nested))
            isolated = scalar_only_call(nested);
        }
        for (unsigned index = argument_offset; index < call->getNumArgs();
             ++index) {
          const auto *argument = call->getArg(index);
          const auto *nested =
              llvm::dyn_cast<clang::CallExpr>(argument->IgnoreParens());
          if (nested != nullptr && !is_numeric_limits_max_call(nested))
            continue;
          if (!stable_scalar_argument(argument, caller) &&
              !(isolated && field_scalar_argument(argument))) {
            fail(argument->getExprLoc(),
                 "nested C++ call arguments require one call and order-independent scalar "
                 "siblings to preserve evaluation order");
            return std::nullopt;
          }
        }
      }
    }

    llvm::json::Array arguments;
    if (receiver != nullptr) {
      auto place = lower_place_reference(receiver, caller);
      if (!place)
        return std::nullopt;
      llvm::json::Object argument;
      argument["kind"] = "reference";
      argument["place"] = std::move(*place);
      arguments.push_back(std::move(argument));
    }
    for (unsigned index = 0; index < definition->getNumParams(); ++index) {
      const auto *source_argument = call->getArg(index + argument_offset);
      const auto *nested =
          llvm::dyn_cast<clang::CallExpr>(source_argument->IgnoreParens());
      std::optional<Json> argument;
      if (allow_nested && nested != nullptr &&
          !is_numeric_limits_max_call(nested)) {
        if (has_receiver ||
            definition->getParamDecl(index)->getType()->isReferenceType() ||
            !context_.hasSameType(source_argument->getType(),
                                  definition->getParamDecl(index)->getType())) {
          fail(source_argument->getExprLoc(),
               "nested C++ calls require a matching scalar value "
               "argument to preserve evaluation order");
          return std::nullopt;
        }
        auto operation = lower_call_operation(nested, caller, true);
        auto value_type = lower_type(nested->getType(), nested->getExprLoc());
        if (!operation || !value_type)
          return std::nullopt;
        llvm::json::Object value;
        value["kind"] = "call";
        value["callee"] = std::move(operation->callee);
        value["arguments"] = std::move(operation->arguments);
        value["value_type"] = std::move(*value_type);
        value["span"] = std::move(operation->span);
        argument = Json(std::move(value));
      } else {
        argument = lower_call_argument(source_argument,
                                       definition->getParamDecl(index), caller);
      }
      if (!argument) {
        return std::nullopt;
      }
      arguments.push_back(std::move(*argument));
    }

    if (!remember_function(definition)) {
      return std::nullopt;
    }

    llvm::json::Object reference;
    reference["declaration_id"] = declaration_id(definition);
    reference["name"] =
        method != nullptr ? method_name(method) : function_name(definition);
    reference["span"] = span(call->getCallee()->getSourceRange());
    // A qualified call of a virtual method runs that method, whatever the
    // receiver's dynamic type.
    if (qualified && method != nullptr && method->isVirtual())
      reference["qualified"] = true;

    Json call_span = span(call->getSourceRange());
    if (!state_.error.empty()) {
      return std::nullopt;
    }
    return LoweredCall{std::move(reference), std::move(arguments),
                       std::move(call_span)};
  }

  std::optional<Json>
  lower_reference_binding(const clang::Expr *expression, clang::QualType reference_type,
                          const clang::FunctionDecl *function) {
    const auto *reference = reference_type->getAs<clang::LValueReferenceType>();
    if (reference == nullptr || !expression->isLValue() ||
        !supported_pointer_element(reference->getPointeeType())) {
      fail(expression->getExprLoc(), "C++ reference results require a native element lvalue");
      return std::nullopt;
    }
    const auto *source = expression->IgnoreParenImpCasts();
    std::optional<Json> address;
    if (const auto *dereference = llvm::dyn_cast<clang::UnaryOperator>(source);
        dereference != nullptr && dereference->getOpcode() == clang::UO_Deref) {
      address = lower_expression(dereference->getSubExpr(), function);
    } else {
      const auto *declaration = llvm::dyn_cast<clang::DeclRefExpr>(source);
      const auto *parameter = declaration == nullptr ? nullptr :
          llvm::dyn_cast<clang::VarDecl>(declaration->getDecl());
      const auto *parameter_reference = parameter == nullptr ? nullptr :
          parameter->getType()->getAs<clang::LValueReferenceType>();
      const bool member = llvm::isa<clang::MemberExpr>(source);
      const bool scalar_object = parameter != nullptr && parameter->hasLocalStorage() &&
          supported_pointer_element(parameter->getType());
      if (!member && (parameter == nullptr || parameter->getDeclContext() != function ||
          (parameter_reference == nullptr && !scalar_object))) {
        fail(expression->getExprLoc(), "C++ references currently bind existing references, automatic native element objects, native element fields, or pointer dereferences");
        return std::nullopt;
      }
      auto place = lower_place_reference(source, function);
      const auto pointee = member || scalar_object ? source->getType() : parameter_reference->getPointeeType();
      auto pointer_type = lower_type(context_.getPointerType(pointee), source->getExprLoc());
      if (!place || !pointer_type) return std::nullopt;
      llvm::json::Object value;
      value["kind"] = "address_of";
      value["place"] = std::move(*place);
      value["value_type"] = std::move(*pointer_type);
      value["span"] = span(source->getSourceRange());
      address = Json(std::move(value));
    }
    auto value_type = lower_type(reference_type, expression->getExprLoc());
    if (!address || !value_type) return std::nullopt;
    llvm::json::Object binding;
    binding["kind"] = "reference_binding";
    binding["address"] = std::move(*address);
    binding["value_type"] = std::move(*value_type);
    binding["span"] = span(expression->getSourceRange());
    return Json(std::move(binding));
  }

  std::optional<Json>
  lower_call_argument(const clang::Expr *argument,
                      const clang::ParmVarDecl *parameter,
                      const clang::FunctionDecl *caller) {
    return lower_call_argument(argument, parameter->getType(),
                               parameter->getLocation(), caller);
  }

  std::optional<Json>
  lower_call_argument(const clang::Expr *argument, clang::QualType parameter_type,
                      clang::SourceLocation parameter_location,
                      const clang::FunctionDecl *caller) {
    if (std_function_prototype(parameter_type) != nullptr)
      return lower_std_function_argument(argument, parameter_type, parameter_location,
                                         caller);
    llvm::json::Object result;
    if (parameter_type->getAsCXXRecordDecl() != nullptr) {
      const auto *construction = llvm::dyn_cast<clang::CXXConstructExpr>(argument->IgnoreParenImpCasts());
      const auto *constructor = construction == nullptr ? nullptr : construction->getConstructor();
      const auto *record = parameter_type->getAsCXXRecordDecl();
      if (constructor == nullptr || !constructor->isCopyConstructor() ||
          !constructor->isTrivial() || constructor->isDeleted() ||
          construction->getNumArgs() != 1 || !construction->getArg(0)->isLValue() ||
          !context_.hasSameUnqualifiedType(construction->getType(), parameter_type) ||
          !record->isTriviallyCopyable() || !record->hasTrivialDestructor()) {
        fail(argument->getExprLoc(), "C++ by-value record arguments require a resolved trivial copy from a live lvalue");
        return std::nullopt;
      }
      auto place = lower_place_reference(construction->getArg(0)->IgnoreParenImpCasts(), caller);
      auto value_type = lower_type(parameter_type, parameter_location);
      if (!place || !value_type) return std::nullopt;
      result["kind"] = "record_copy";
      result["place"] = std::move(*place);
      result["value_type"] = std::move(*value_type);
      result["span"] = span(argument->getSourceRange());
      return Json(std::move(result));
    }
    if (parameter_type->getAs<clang::LValueReferenceType>() != nullptr) {
      auto place = lower_place_reference(argument, caller);
      if (!place) {
        return std::nullopt;
      }
      result["kind"] = "reference";
      result["place"] = std::move(*place);
      return Json(std::move(result));
    }
    if (parameter_type->getAs<clang::PointerType>() != nullptr) {
      auto value = lower_expression(argument, caller);
      if (!value) {
        return std::nullopt;
      }
      result["kind"] = "value";
      result["value"] = std::move(*value);
      return Json(std::move(result));
    }
    if (!parameter_type.hasQualifiers() &&
        (context_.hasSameType(parameter_type, context_.BoolTy) ||
         supported_scalar_value_type(parameter_type))) {
      auto value = lower_expression(argument, caller);
      if (!value) {
        return std::nullopt;
      }
      result["kind"] = "value";
      result["value"] = std::move(*value);
      return Json(std::move(result));
    }
    fail(argument->getExprLoc(),
         "unsupported argument in the direct C++ call slice");
    return std::nullopt;
  }

  std::optional<llvm::json::Array>
  lower_branch(const clang::Stmt *statement,
               const clang::FunctionDecl *function,
               CleanupScopeKind cleanup_scope) {
    llvm::json::Array result;
    if (statement == nullptr || is_checked_runtime_noop(statement)) {
      return result;
    }
    statement = without_branch_weights(statement);
    if (!statement) return std::nullopt;
    if (const auto *compound = llvm::dyn_cast<clang::CompoundStmt>(statement)) {
      bool has_direct_destructible_object = false;
      for (const clang::Stmt *member : compound->body()) {
        const auto *declarations = llvm::dyn_cast<clang::DeclStmt>(member);
        const auto *local =
            declarations != nullptr && declarations->isSingleDecl()
                ? llvm::dyn_cast<clang::VarDecl>(declarations->getSingleDecl())
                : nullptr;
        const auto *record_type =
            local == nullptr ? nullptr : local->getType()->getAs<clang::RecordType>();
        const auto *record =
            record_type == nullptr
                ? nullptr
                : llvm::dyn_cast<clang::CXXRecordDecl>(
                      record_type->getDecl()->getDefinition());
        const clang::CXXDestructorDecl *destructor =
            record == nullptr ? nullptr : record->getDestructor();
        has_direct_destructible_object |=
            needs_destructor_body(destructor);
      }
      if (cleanup_scope != CleanupScopeKind::None &&
          has_direct_destructible_object) {
        auto lowered = lower_scope(
            compound, function,
            cleanup_scope == CleanupScopeKind::Conditional);
        if (!lowered) {
          return std::nullopt;
        }
        result.push_back(std::move(*lowered));
        return result;
      }
      for (const clang::Stmt *member : compound->body()) {
        if (is_checked_runtime_noop(member)) continue;
        auto lowered = lower_statement(member, function, false, false);
        if (!lowered) {
          return std::nullopt;
        }
        result.push_back(std::move(*lowered));
      }
      return result;
    }
    auto lowered = lower_statement(statement, function, false, false);
    if (!lowered) {
      return std::nullopt;
    }
    result.push_back(std::move(*lowered));
    return result;
  }

  // The parameter name a generic template's abstract type argument stands
  // for, when `type` is one.
  const std::string *archetype_name(clang::QualType type) const {
    const auto *record = type.isNull() ? nullptr : type->getAsCXXRecordDecl();
    if (record == nullptr)
      return nullptr;
    for (const auto &[name, archetype] : archetypes_)
      if (archetype->getCanonicalDecl() == record->getCanonicalDecl())
        return &name;
    return nullptr;
  }

  // Whether `type` names an abstract type argument, directly, through a
  // pointer, reference or array, or as an argument of a class template.
  bool mentions_archetype(clang::QualType type) const {
    if (type.isNull())
      return false;
    if (archetype_name(type) != nullptr)
      return true;
    if (const auto *reference = type->getAs<clang::ReferenceType>())
      return mentions_archetype(reference->getPointeeType());
    if (const auto *pointer = type->getAs<clang::PointerType>())
      return mentions_archetype(pointer->getPointeeType());
    if (const auto *array = context_.getAsArrayType(type))
      return mentions_archetype(array->getElementType());
    if (const auto *instance = llvm::dyn_cast_or_null<clang::ClassTemplateSpecializationDecl>(
            type->getAsCXXRecordDecl()))
      for (const clang::TemplateArgument &argument : instance->getTemplateArgs().asArray())
        if (argument.getKind() == clang::TemplateArgument::Type &&
            mentions_archetype(argument.getAsType()))
          return true;
    return false;
  }

  // `printed`, a Clang spelling, with each abstract type argument written as
  // the parameter it stands for: `Stack<__click_T>` is `Stack<T>`.
  std::string without_archetypes(std::string printed) const {
    for (const auto &[name, archetype] : archetypes_) {
      const std::string spelled = archetype_record_name(name);
      std::size_t at = 0;
      while ((at = printed.find(spelled, at)) != std::string::npos) {
        const std::size_t end = at + spelled.size();
        if (end < printed.size() &&
            (std::isalnum(static_cast<unsigned char>(printed[end])) || printed[end] == '_')) {
          at = end;
          continue;
        }
        printed.replace(at, spelled.size(), name);
        at += name.size();
      }
    }
    return printed;
  }

  // Each generic class template the options name, checked to take type
  // parameters only, as many as the options name.
  bool resolve_generic_templates() {
    for (const GenericTemplate &generic : generic_templates_) {
      const auto found = class_templates_.find(generic.qualified_name);
      if (found == class_templates_.end()) {
        fail({}, "generic class template `" + generic.qualified_name + "` was not found");
        return false;
      }
      const clang::TemplateParameterList *parameters =
          found->second->getTemplateParameters();
      bool types = parameters->size() == generic.parameters.size();
      for (const clang::NamedDecl *parameter : *parameters) {
        const auto *type = llvm::dyn_cast<clang::TemplateTypeParmDecl>(parameter);
        types = types && type != nullptr && !type->isParameterPack() &&
                !type->hasDefaultArgument();
      }
      if (!types) {
        fail(found->second->getLocation(),
             "a generic class template takes the type parameters its options name, "
             "with no defaults, packs or non-type parameters");
        return false;
      }
      for (const std::string &name : generic.parameters)
        if (archetypes_.find(name) == archetypes_.end()) {
          fail(found->second->getLocation(),
               "the abstract type `" + name + "` was not declared");
          return false;
        }
      generic_by_template_.emplace(found->second, &generic);
    }
    return true;
  }

  // The generic class template `declaration`'s instance at its abstract
  // type arguments, instantiated once.
  const clang::ClassTemplateSpecializationDecl *
  archetype_instance(const clang::ClassTemplateDecl *declaration,
                     clang::SourceLocation location) {
    if (const auto found = archetype_instances_.find(declaration);
        found != archetype_instances_.end())
      return found->second;
    const GenericTemplate &generic = *generic_by_template_.at(declaration);
    clang::TemplateArgumentListInfo arguments(location, location);
    for (const std::string &name : generic.parameters) {
      const clang::QualType type = context_.getRecordType(archetypes_.at(name));
      arguments.addArgument(clang::TemplateArgumentLoc(
          clang::TemplateArgument(type), context_.getTrivialTypeSourceInfo(type, location)));
    }
    clang::Sema &sema = compiler_.getSema();
    const bool errors = context_.getDiagnostics().hasErrorOccurred();
    const clang::QualType type = sema.CheckTemplateIdType(
        clang::TemplateName(const_cast<clang::ClassTemplateDecl *>(declaration)), location,
        arguments);
    if (type.isNull() ||
        sema.RequireCompleteType(location, type, clang::diag::err_incomplete_type) ||
        (!errors && context_.getDiagnostics().hasErrorOccurred())) {
      fail(location, "`" + generic.qualified_name +
                         "` cannot be instantiated at abstract type arguments");
      return nullptr;
    }
    const auto *instance = llvm::dyn_cast_or_null<clang::ClassTemplateSpecializationDecl>(
        type->getAsCXXRecordDecl());
    if (instance == nullptr) {
      fail(location, "`" + generic.qualified_name +
                         "` at abstract type arguments is not a class template instance");
      return nullptr;
    }
    archetype_instances_.emplace(declaration, instance);
    return instance;
  }

  // The definition at abstract type arguments of `declaration`, a written
  // method of a generic class template's instance at other arguments: the
  // same member of the same template, which is verified for every type
  // argument. Null when `declaration` is no such method or failed.
  const clang::FunctionDecl *generic_counterpart(const clang::FunctionDecl *declaration) {
    const auto *method = llvm::dyn_cast<clang::CXXMethodDecl>(declaration);
    if (method == nullptr || method->isImplicit() || method->isDefaulted())
      return nullptr;
    const auto *instance =
        llvm::dyn_cast<clang::ClassTemplateSpecializationDecl>(method->getParent());
    if (instance == nullptr)
      return nullptr;
    const auto *declared = instance->getSpecializedTemplate()->getCanonicalDecl();
    if (generic_by_template_.find(declared) == generic_by_template_.end() ||
        mentions_archetype(context_.getRecordType(instance)))
      return nullptr;
    // The instance must be the template's own body at its arguments: an
    // explicit or partial specialization is another body.
    if (instance->getSpecializationKind() == clang::TSK_ExplicitSpecialization ||
        instance->getSpecializedTemplateOrPartial()
            .is<clang::ClassTemplatePartialSpecializationDecl *>() ||
        method->getTemplateSpecializationKind() == clang::TSK_ExplicitSpecialization ||
        method->getPrimaryTemplate() != nullptr) {
      fail(method->getLocation(),
           "a generic class template's instance method is its template's own "
           "method, not a specialization or a member template");
      return nullptr;
    }
    const clang::FunctionDecl *pattern = method->getInstantiatedFromMemberFunction();
    const auto *archetype = archetype_instance(declared, method->getLocation());
    if (pattern == nullptr || archetype == nullptr)
      return nullptr;
    for (const clang::Decl *member : archetype->decls()) {
      const auto *candidate = llvm::dyn_cast<clang::FunctionDecl>(member);
      if (candidate == nullptr || candidate->getInstantiatedFromMemberFunction() == nullptr ||
          candidate->getInstantiatedFromMemberFunction()->getCanonicalDecl() !=
              pattern->getCanonicalDecl())
        continue;
      clang::Sema &sema = compiler_.getSema();
      const bool errors = context_.getDiagnostics().hasErrorOccurred();
      sema.InstantiateFunctionDefinition(method->getLocation(),
                                         const_cast<clang::FunctionDecl *>(candidate),
                                         /*Recursive=*/true, /*DefinitionRequired=*/true,
                                         /*AtEndOfTU=*/true);
      sema.PerformPendingInstantiations();
      const clang::FunctionDecl *definition = candidate->getDefinition();
      if (definition == nullptr ||
          (!errors && context_.getDiagnostics().hasErrorOccurred())) {
        fail(method->getLocation(),
             "`" + without_archetypes(definition == nullptr
                                          ? candidate->getQualifiedNameAsString()
                                          : definition->getQualifiedNameAsString()) +
                 "` cannot be instantiated at abstract type arguments");
        return nullptr;
      }
      return definition;
    }
    fail(method->getLocation(),
         "a generic class template's method has no instance at abstract type arguments");
    return nullptr;
  }

  // Whether `function` is a body at abstract type arguments: a method of a
  // record that names one.
  bool is_generic_body(const clang::FunctionDecl *function) const {
    const auto *method = llvm::dyn_cast<clang::CXXMethodDecl>(function);
    return method != nullptr && mentions_archetype(context_.getRecordType(method->getParent()));
  }

  // A generic body's template pattern must mean the same at every type
  // argument: nothing in it may compute a value, choose a branch or name a
  // member from a template argument, beyond the types of the values it
  // copies.
  bool check_generic_pattern(const clang::FunctionDecl *function) {
    const clang::FunctionDecl *pattern = function->getTemplateInstantiationPattern();
    if (pattern == nullptr) {
      fail(function->getLocation(),
           "a body at abstract type arguments has no template pattern");
      return false;
    }
    if (!checked_generic_patterns_.insert(pattern->getCanonicalDecl()).second)
      return true;
    struct DependentUses : clang::RecursiveASTVisitor<DependentUses> {
      const clang::Stmt *found = nullptr;
      const char *reason = nullptr;
      bool refuse(const clang::Stmt *statement, const char *why) {
        found = statement;
        reason = why;
        return false;
      }
      bool VisitIfStmt(clang::IfStmt *statement) {
        if (statement->isConstexpr())
          return refuse(statement, "an `if constexpr`");
        return true;
      }
      bool VisitUnaryExprOrTypeTraitExpr(clang::UnaryExprOrTypeTraitExpr *expression) {
        if (expression->isValueDependent())
          return refuse(expression, "a size or alignment of a template argument");
        return true;
      }
      bool VisitTypeTraitExpr(clang::TypeTraitExpr *expression) {
        if (expression->isValueDependent())
          return refuse(expression, "a type trait of a template argument");
        return true;
      }
      bool VisitCXXNoexceptExpr(clang::CXXNoexceptExpr *expression) {
        if (expression->isValueDependent())
          return refuse(expression, "a `noexcept` test of a template argument");
        return true;
      }
      bool VisitDependentScopeDeclRefExpr(clang::DependentScopeDeclRefExpr *expression) {
        return refuse(expression, "a name in a template argument's scope");
      }
      bool VisitCXXUnresolvedConstructExpr(clang::CXXUnresolvedConstructExpr *expression) {
        return refuse(expression, "a construction or conversion of a template argument");
      }
      bool VisitExplicitCastExpr(clang::ExplicitCastExpr *expression) {
        if (expression->isTypeDependent() || expression->isValueDependent())
          return refuse(expression, "a cast involving a template argument");
        return true;
      }
      bool VisitConceptSpecializationExpr(clang::ConceptSpecializationExpr *expression) {
        return refuse(expression, "a concept test");
      }
      bool VisitRequiresExpr(clang::RequiresExpr *expression) {
        return refuse(expression, "a `requires` expression");
      }
      bool VisitDeclRefExpr(clang::DeclRefExpr *expression) {
        const auto *variable = llvm::dyn_cast<clang::VarDecl>(expression->getDecl());
        if (variable != nullptr && variable->isStaticDataMember() &&
            variable->getDeclContext()->isDependentContext())
          return refuse(expression, "a static member of a template");
        return true;
      }
      bool VisitMemberExpr(clang::MemberExpr *expression) {
        const auto *variable = llvm::dyn_cast<clang::VarDecl>(expression->getMemberDecl());
        if (variable != nullptr && variable->isStaticDataMember())
          return refuse(expression, "a static member of a template");
        return true;
      }
    } uses;
    uses.TraverseStmt(pattern->getBody());
    if (uses.found != nullptr) {
      fail(uses.found->getBeginLoc(),
           std::string("a template verified for every type argument has ") + uses.reason +
               ", which may mean something else at each type");
      return false;
    }
    return true;
  }

  // Each class template a generic body uses at abstract type arguments has
  // one body for every argument: no explicit or partial specialization of
  // it, or of its members.
  bool check_unspecialized(const clang::ClassTemplateDecl *declaration) {
    llvm::SmallVector<clang::ClassTemplatePartialSpecializationDecl *, 4> partial;
    const_cast<clang::ClassTemplateDecl *>(declaration)->getPartialSpecializations(partial);
    bool specialized = !partial.empty();
    for (const clang::ClassTemplateSpecializationDecl *instance :
         declaration->specializations()) {
      specialized = specialized ||
                    instance->getSpecializationKind() == clang::TSK_ExplicitSpecialization;
      for (const clang::Decl *member : instance->decls())
        if (const auto *function = llvm::dyn_cast<clang::FunctionDecl>(member))
          specialized = specialized || function->getTemplateSpecializationKind() ==
                                           clang::TSK_ExplicitSpecialization;
    }
    if (specialized) {
      fail(declaration->getLocation(),
           "`" + declaration->getQualifiedNameAsString() +
               "` is used at abstract type arguments, so it may not be specialized");
      return false;
    }
    return true;
  }

  bool check_generic_records() {
    for (const clang::CXXRecordDecl *record : record_definitions_) {
      const auto *instance = llvm::dyn_cast<clang::ClassTemplateSpecializationDecl>(record);
      if (instance != nullptr && mentions_archetype(context_.getRecordType(instance)) &&
          !check_unspecialized(instance->getSpecializedTemplate()->getCanonicalDecl()))
        return false;
    }
    return true;
  }

  bool remember_function(const clang::FunctionDecl *definition) {
    if (known_functions_.insert(definition->getCanonicalDecl()).second) {
      if (reachable_definitions_.size() + 1 >= kMaxFunctionDeclarations) {
        fail(definition->getLocation(),
             "C++ artifact budget exhausted: function declarations (limit " +
                 std::to_string(kMaxFunctionDeclarations) + ")");
        return false;
      }
      reachable_definitions_.push_back(definition);
    }
    return true;
  }

  bool remember_constant(const clang::VarDecl *constant) {
    const clang::VarDecl *definition =
        constant == nullptr ? nullptr : constant->getDefinition();
    if (definition == nullptr) {
      fail({}, "reachable C++ constant has no definition");
      return false;
    }
    definition = definition->getCanonicalDecl();
    const bool internal_namespace_constant =
        definition->getDeclContext()->isFileContext() &&
        definition->getFormalLinkage() == clang::Linkage::Internal;
    if (!definition->isConstexpr() ||
        (definition->getStorageClass() != clang::SC_Static &&
         !internal_namespace_constant &&
         !(definition->isInline() && definition->getDeclContext()->isFileContext())) ||
        !definition->hasGlobalStorage()) {
      fail(definition->getLocation(),
           "reachable C++ constants must be namespace-scope static constexpr "
           "or internal-linkage/inline constexpr declarations");
      return false;
    }
    const clang::QualType type = definition->getType();
    if (!type.isConstQualified() || !type->isIntegerType() ||
        context_.getTypeSize(type) != 64) {
      fail(definition->getLocation(),
           "reachable C++ constants must have const signed or unsigned 64-bit type");
      return false;
    }
    if (known_constants_.insert(definition).second) {
      if (constant_definitions_.size() >= kMaxConstantDeclarations) {
        fail(definition->getLocation(),
             "C++ artifact budget exhausted: constant declarations (limit " +
                 std::to_string(kMaxConstantDeclarations) + ")");
        return false;
      }
      constant_definitions_.push_back(definition);
    }
    return true;
  }

  bool discover_constant_dependencies(const clang::Stmt *statement) {
    if (statement == nullptr) {
      fail({}, "reachable C++ constant has no initializer");
      return false;
    }
    if (const auto *reference = llvm::dyn_cast<clang::DeclRefExpr>(statement)) {
      if (const auto *variable =
              llvm::dyn_cast<clang::VarDecl>(reference->getDecl());
          variable != nullptr && variable->hasGlobalStorage() &&
          !remember_constant(variable)) {
        return false;
      }
    }
    for (const clang::Stmt *child : statement->children()) {
      if (!discover_constant_dependencies(child)) {
        return false;
      }
    }
    return true;
  }

  std::optional<Json>
  lower_constant(const clang::VarDecl *constant,
                 const clang::FunctionDecl *function) {
    auto source = executable_source(constant->getLocation());
    if (!source) {
      fail(constant->getLocation(), "C++ constants require a selected or dependency source");
      return std::nullopt;
    }
    llvm::SaveAndRestore<std::string> constant_source(function_source_, *source);
    if (*source != logical_source_) dependency_sources_.insert(*source);
    const clang::Expr *initializer = constant->getInit();
    const clang::Expr *semantic =
        initializer == nullptr ? nullptr : initializer->IgnoreParenImpCasts();
    const auto *binary = llvm::dyn_cast_or_null<clang::BinaryOperator>(semantic);
    const auto *cast = llvm::dyn_cast_or_null<clang::ExplicitCastExpr>(semantic);
    const auto *operand = cast == nullptr ? nullptr : cast->getSubExpr()->IgnoreParenImpCasts();
    const auto *negation = llvm::dyn_cast_or_null<clang::UnaryOperator>(operand);
    const bool unsigned_literal_cast = constant->getType()->isUnsignedIntegerType() &&
        cast != nullptr &&
        (cast->getCastKind() == clang::CK_IntegralCast ||
         (cast->getCastKind() == clang::CK_NoOp &&
          context_.hasSameType(cast->getType(), cast->getSubExpr()->getType()))) &&
        (llvm::isa_and_nonnull<clang::IntegerLiteral>(operand) ||
         (negation != nullptr && negation->getOpcode() == clang::UO_Minus &&
          llvm::isa<clang::IntegerLiteral>(negation->getSubExpr()->IgnoreParenImpCasts())));
    if (semantic == nullptr ||
        (!unsigned_literal_cast && !llvm::isa<clang::IntegerLiteral>(semantic) &&
         (binary == nullptr || binary->getOpcode() != clang::BO_Mul))) {
      fail(constant->getLocation(),
           "supported C++ constants require a literal leaf or one dependent multiplication");
      return std::nullopt;
    }
    auto value_type =
        lower_type(constant->getType(), constant->getLocation(),
                   direct_source_alias(constant->getTypeSourceInfo()));
    auto lowered_initializer = lower_expression(initializer, function);
    const clang::APValue *evaluated = constant->evaluateValue();
    if (!value_type || !lowered_initializer || evaluated == nullptr ||
        !evaluated->isInt()) {
      if (state_.error.empty()) {
        fail(constant->getLocation(),
             "Clang could not evaluate the supported C++ constant");
      }
      return std::nullopt;
    }
    llvm::SmallString<32> evaluated_value;
    evaluated->getInt().toString(evaluated_value, 10);
    llvm::json::Object result;
    result["declaration_id"] = declaration_id(constant);
    result["name"] = constant->getNameAsString();
    result["value_type"] = std::move(*value_type);
    result["initializer"] = std::move(*lowered_initializer);
    result["evaluated_value"] = evaluated_value.str().str();
    result["span"] = span(constant->getSourceRange());
    if (!state_.error.empty()) {
      return std::nullopt;
    }
    return Json(std::move(result));
  }

  std::optional<Json>
  lower_constant_reference(const clang::DeclRefExpr *reference,
                           const clang::ImplicitCastExpr *cast) {
    const auto *constant =
        llvm::dyn_cast<clang::VarDecl>(reference->getDecl());
    if (!remember_constant(constant)) {
      return std::nullopt;
    }
    auto value_type = lower_type(cast->getType().getUnqualifiedType(), cast->getExprLoc());
    if (!value_type) {
      return std::nullopt;
    }
    llvm::json::Object constant_reference;
    constant_reference["declaration_id"] = declaration_id(constant);
    constant_reference["name"] = constant->getNameAsString();
    constant_reference["span"] = span(reference->getSourceRange());
    llvm::json::Object result;
    result["kind"] = "constant_reference";
    result["constant"] = std::move(constant_reference);
    result["value_type"] = std::move(*value_type);
    result["span"] = span(cast->getSourceRange());
    if (!state_.error.empty()) {
      return std::nullopt;
    }
    return Json(std::move(result));
  }

  // These calls already have distinct compiler-constant semantics. Preserve
  // that allowlist before recognizing a runtime return-call operation.
  bool is_numeric_limits_max_call(const clang::CallExpr *call) const {
    const auto *method =
        call == nullptr ? nullptr
                        : llvm::dyn_cast_or_null<clang::CXXMethodDecl>(
                              call->getDirectCallee());
    return method != nullptr && method->isStatic() && method->isConstexpr() &&
           call->getNumArgs() == 0 && method->getNameAsString() == "max" &&
           method->getParent()->getNameAsString() == "numeric_limits" &&
           method->getParent()->getQualifiedNameAsString().rfind(
               "std::numeric_limits", 0) == 0;
  }

  // The function an expression designates as a pointer value: `&f`, or `f`
  // decayed to a pointer.
  const clang::FunctionDecl *designated_function(const clang::Expr *expression) const {
    expression = expression->IgnoreParens();
    const clang::Expr *operand = nullptr;
    if (const auto *cast = llvm::dyn_cast<clang::ImplicitCastExpr>(expression);
        cast != nullptr && cast->getCastKind() == clang::CK_FunctionToPointerDecay)
      operand = cast->getSubExpr();
    else if (const auto *address = llvm::dyn_cast<clang::UnaryOperator>(expression);
             address != nullptr && address->getOpcode() == clang::UO_AddrOf)
      operand = address->getSubExpr();
    const auto *reference =
        operand == nullptr ? nullptr : llvm::dyn_cast<clang::DeclRefExpr>(operand->IgnoreParens());
    return reference == nullptr ? nullptr
                                : llvm::dyn_cast<clang::FunctionDecl>(reference->getDecl());
  }

  // The value passed for a `std::function` parameter: a lambda, whose
  // creation captures its by-copy captures; a function, by its address; or
  // another `std::function` parameter or local, by its value. Clang writes a
  // conversion as the construction of a `std::function` temporary, which
  // Click does not model: the temporary only holds the callable.
  std::optional<Json> lower_std_function_argument(const clang::Expr *argument,
                                                  clang::QualType parameter_type,
                                                  clang::SourceLocation parameter_location,
                                                  const clang::FunctionDecl *caller) {
    const clang::Expr *source = argument;
    for (;;) {
      source = source->IgnoreParens();
      if (const auto *cleanups = llvm::dyn_cast<clang::ExprWithCleanups>(source))
        source = cleanups->getSubExpr();
      else if (const auto *temporary = llvm::dyn_cast<clang::MaterializeTemporaryExpr>(source))
        source = temporary->getSubExpr();
      else if (const auto *bound = llvm::dyn_cast<clang::CXXBindTemporaryExpr>(source))
        source = bound->getSubExpr();
      else if (const auto *cast = llvm::dyn_cast<clang::ImplicitCastExpr>(source);
               cast != nullptr && (cast->getCastKind() == clang::CK_NoOp ||
                                   cast->getCastKind() == clang::CK_ConstructorConversion))
        source = cast->getSubExpr();
      else if (const auto *construction = llvm::dyn_cast<clang::CXXConstructExpr>(source);
               construction != nullptr && construction->getNumArgs() == 1 &&
               std_function_prototype(construction->getType()) != nullptr)
        source = construction->getArg(0);
      else
        break;
    }
    auto value_type = lower_type(parameter_type, parameter_location);
    if (!value_type)
      return std::nullopt;
    std::optional<Json> value;
    if (const auto *lambda = llvm::dyn_cast<clang::LambdaExpr>(source))
      value = lower_closure_creation(lambda, std::move(*value_type), caller);
    else if (const auto *designated = designated_function(source))
      value = lower_function_address(source, designated);
    else if (const auto *reference = llvm::dyn_cast<clang::DeclRefExpr>(source);
             reference != nullptr && std_function_prototype(source->getType()) != nullptr) {
      // A `std::function` parameter or local passed on is a load of the
      // callable it holds; Clang writes no lvalue-to-rvalue cast of a record.
      auto place = lower_place_reference(source, caller);
      auto loaded_type = lower_type(source->getType(), source->getExprLoc());
      if (!place || !loaded_type)
        return std::nullopt;
      llvm::json::Object load;
      load["kind"] = "load";
      load["place"] = std::move(*place);
      load["value_type"] = std::move(*loaded_type);
      load["span"] = span(source->getSourceRange());
      value = Json(std::move(load));
    }
    else {
      fail(argument->getExprLoc(),
           "a C++ std::function argument must be a lambda, a function, or a "
           "std::function parameter or local");
      return std::nullopt;
    }
    if (!value)
      return std::nullopt;
    llvm::json::Object result;
    result["kind"] = "value";
    result["value"] = std::move(*value);
    return Json(std::move(result));
  }

  // The captures a lambda passed for a `std::function` holds: each a by-copy
  // capture of a scalar local or parameter, read when the lambda is made.
  // A capture by reference is refused: C++ does not keep the variable from
  // changing while the closure lives.
  std::optional<std::vector<const clang::VarDecl *>>
  lambda_captures(const clang::CXXRecordDecl *closure, clang::SourceLocation location) {
    std::vector<const clang::VarDecl *> captures;
    for (const clang::LambdaCapture &capture : closure->captures()) {
      const auto *variable =
          capture.capturesVariable()
              ? llvm::dyn_cast<clang::VarDecl>(capture.getCapturedVar())
              : nullptr;
      if (variable == nullptr || capture.getCaptureKind() != clang::LCK_ByCopy ||
          !variable->hasLocalStorage() || variable->getType()->isReferenceType() ||
          !(supported_scalar_value_type(variable->getType().getUnqualifiedType()) ||
            context_.hasSameType(variable->getType().getUnqualifiedType(), context_.BoolTy))) {
        fail(location,
             "a C++ lambda captures only scalar locals and parameters, by copy");
        return std::nullopt;
      }
      captures.push_back(variable);
    }
    return captures;
  }

  // A lambda passed for a `std::function`: one that captures nothing is its
  // call operator's address; one that captures is a closure creation from
  // the captured values.
  std::optional<Json> lower_closure_creation(const clang::LambdaExpr *lambda, Json value_type,
                                             const clang::FunctionDecl *caller) {
    const clang::CXXRecordDecl *closure = lambda->getLambdaClass();
    const clang::CXXMethodDecl *call = lambda->getCallOperator();
    if (call->getTemplatedKind() != clang::FunctionDecl::TK_NonTemplate) {
      fail(lambda->getExprLoc(), "a C++ lambda passed for a std::function must not be generic");
      return std::nullopt;
    }
    auto captures = lambda_captures(closure, lambda->getExprLoc());
    auto name = lambda_name(call);
    if (!captures || !name || !remember_function(call))
      return std::nullopt;
    llvm::json::Object reference;
    reference["declaration_id"] = declaration_id(call);
    reference["name"] = *name;
    reference["span"] = span(lambda->getSourceRange());
    llvm::json::Object result;
    result["function"] = std::move(reference);
    result["value_type"] = std::move(value_type);
    result["span"] = span(lambda->getSourceRange());
    if (captures->empty()) {
      result["kind"] = "function_address";
    } else {
      llvm::json::Array values;
      for (const clang::Expr *initializer : lambda->capture_inits()) {
        auto value = lower_expression(initializer, caller);
        if (!value)
          return std::nullopt;
        values.push_back(std::move(*value));
      }
      result["kind"] = "closure_instance";
      result["captures"] = std::move(values);
    }
    if (!state_.error.empty())
      return std::nullopt;
    return Json(std::move(result));
  }

  // Whether every temporary `expression` binds for destruction is a
  // `std::function`, which Click models as the callable it holds, so its
  // destruction has no effect Click models. Lambda bodies are not searched.
  bool only_std_function_temporaries(const clang::Expr *expression) {
    struct Finder : clang::RecursiveASTVisitor<Finder> {
      const SemanticExporter *self;
      bool other = false;
      bool TraverseLambdaExpr(clang::LambdaExpr *) { return true; }
      bool VisitCXXBindTemporaryExpr(clang::CXXBindTemporaryExpr *bound) {
        if (self->std_function_prototype(bound->getType()) == nullptr)
          other = true;
        return !other;
      }
    } finder;
    finder.self = this;
    finder.TraverseStmt(const_cast<clang::Expr *>(expression));
    return !finder.other;
  }

  // A lambda converted to a function pointer, `apply([](int y) noexcept {
  // return y + y; }, x)`: Clang writes the conversion as a call of the
  // closure type's conversion function on the lambda.
  const clang::LambdaExpr *converted_lambda(const clang::Expr *expression) {
    const auto *cast = llvm::dyn_cast<clang::ImplicitCastExpr>(expression->IgnoreParens());
    if (cast == nullptr || cast->getCastKind() != clang::CK_UserDefinedConversion)
      return nullptr;
    const auto *call =
        llvm::dyn_cast<clang::CXXMemberCallExpr>(cast->getSubExpr()->IgnoreParens());
    if (call == nullptr || !llvm::isa<clang::CXXConversionDecl>(call->getMethodDecl()))
      return nullptr;
    return llvm::dyn_cast<clang::LambdaExpr>(
        call->getImplicitObjectArgument()->IgnoreImplicit()->IgnoreParens());
  }

  // The name of a lambda's call operator: the enclosing function's, then the
  // lambda's index among the lambdas written in that function's body, in
  // source order. A sidecar spells it `caller::(lambda#0)`. The importer's
  // own names never contain a double underscore, so no function has it.
  std::optional<std::string> lambda_name(const clang::CXXMethodDecl *call) {
    const clang::CXXRecordDecl *closure = call->getParent();
    const auto *enclosing =
        llvm::dyn_cast_or_null<clang::FunctionDecl>(closure->getDeclContext());
    if (enclosing == nullptr || llvm::isa<clang::CXXMethodDecl>(enclosing) ||
        enclosing->getBody() == nullptr) {
      fail(call->getLocation(),
           "a C++ lambda is supported only in the body of a free function");
      return std::nullopt;
    }
    struct Collector : clang::RecursiveASTVisitor<Collector> {
      std::vector<const clang::CXXRecordDecl *> closures;
      bool VisitLambdaExpr(clang::LambdaExpr *lambda) {
        closures.push_back(lambda->getLambdaClass());
        return true;
      }
    } collector;
    collector.TraverseStmt(enclosing->getBody());
    const auto found =
        std::find(collector.closures.begin(), collector.closures.end(), closure);
    if (found == collector.closures.end()) {
      fail(call->getLocation(), "a C++ lambda's enclosing body does not contain it");
      return std::nullopt;
    }
    return function_name(enclosing) + "__lambda_" +
           std::to_string(found - collector.closures.begin());
  }

  // A declaration's C++ path, segment by segment, as a sidecar writes it:
  // `Square::area` is ["Square", "area"], a constructor `Rec::Rec`, a
  // destructor `Rec::~Rec`, an operator `Rec::operator+=`, a template
  // instance `Stored<long long>::Read` or `choose<true>`, and the first
  // lambda in `caller` `caller::(lambda#0)`. The importer names each
  // declaration by its path.
  llvm::json::Array function_path(const clang::FunctionDecl *function) {
    std::vector<std::string> segments;
    const auto *method = llvm::dyn_cast<clang::CXXMethodDecl>(function);
    if (method != nullptr && method->getParent()->isLambda()) {
      const auto *enclosing = llvm::dyn_cast_or_null<clang::FunctionDecl>(
          method->getParent()->getDeclContext());
      const auto name = lambda_name(method);
      if (enclosing == nullptr || !name)
        return {};
      llvm::json::Array path = function_path(enclosing);
      const std::string marker = "__lambda_";
      path.push_back("(lambda#" + name->substr(name->rfind(marker) + marker.size()) + ")");
      return path;
    }
    context_segments(function->getDeclContext(), segments);
    std::string own;
    if (const auto *constructor = llvm::dyn_cast<clang::CXXConstructorDecl>(function))
      own = constructor->getParent()->getNameAsString();
    else if (const auto *destructor = llvm::dyn_cast<clang::CXXDestructorDecl>(function))
      own = "~" + destructor->getParent()->getNameAsString();
    else
      own = function->getNameAsString();
    if (const auto *arguments = function->getTemplateSpecializationArgs()) {
      const auto *primary = function->getPrimaryTemplate();
      own += printed_template_arguments(
          arguments->asArray(),
          primary != nullptr ? primary->getTemplateParameters() : nullptr);
    }
    segments.push_back(own);
    llvm::json::Array path;
    for (const std::string &segment : segments)
      path.push_back(segment);
    return path;
  }

  llvm::json::Array record_path(const clang::CXXRecordDecl *record) {
    std::vector<std::string> segments;
    context_segments(record->getDeclContext(), segments);
    segments.push_back(record_segment(record));
    llvm::json::Array path;
    for (const std::string &segment : segments)
      path.push_back(segment);
    return path;
  }

  // The enclosing namespaces and classes of a declaration, outermost first.
  void context_segments(const clang::DeclContext *context,
                        std::vector<std::string> &segments) {
    std::vector<std::string> inner;
    for (; context != nullptr && !context->isTranslationUnit();
         context = context->getParent()) {
      if (const auto *space = llvm::dyn_cast<clang::NamespaceDecl>(context)) {
        if (space->isInline())
          continue;
        inner.push_back(space->isAnonymousNamespace() ? "(anonymous namespace)"
                                                      : space->getNameAsString());
      } else if (const auto *record = llvm::dyn_cast<clang::CXXRecordDecl>(context)) {
        inner.push_back(record_segment(record));
      }
    }
    segments.insert(segments.end(), inner.rbegin(), inner.rend());
  }

  std::string record_segment(const clang::CXXRecordDecl *record) {
    std::string segment = record->getNameAsString();
    if (const auto *instance =
            llvm::dyn_cast<clang::ClassTemplateSpecializationDecl>(record))
      segment += printed_template_arguments(
          instance->getTemplateArgs().asArray(),
          instance->getSpecializedTemplate()->getTemplateParameters());
    return segment;
  }

  // Template arguments as Clang prints them against their parameters,
  // `<long long, true>`: a trailing argument equal to its default is left
  // out and an integer is printed without a suffix, so `std::span<int>` and
  // `std::span<int, 4>` are spelled as C++ source writes them.
  std::string printed_template_arguments(llvm::ArrayRef<clang::TemplateArgument> arguments,
                                         const clang::TemplateParameterList *parameters) {
    std::string printed;
    llvm::raw_string_ostream stream(printed);
    clang::PrintingPolicy policy = context_.getPrintingPolicy();
    policy.SuppressTagKeyword = true;
    clang::printTemplateArgumentList(stream, arguments, policy, parameters);
    return without_archetypes(stream.str());
  }

  // A lambda that captures nothing, converted to a function pointer, is the
  // address of its call operator, which is exported as a free function.
  std::optional<Json> lower_lambda_address(const clang::Expr *expression,
                                           const clang::LambdaExpr *lambda) {
    const clang::CXXRecordDecl *closure = lambda->getLambdaClass();
    const clang::CXXMethodDecl *call = lambda->getCallOperator();
    if (lambda->capture_size() != 0 || !closure->field_empty() ||
        call->getTemplatedKind() != clang::FunctionDecl::TK_NonTemplate) {
      fail(expression->getExprLoc(),
           "a C++ lambda converted to a function pointer must capture nothing "
           "and must not be generic");
      return std::nullopt;
    }
    auto name = lambda_name(call);
    auto value_type = lower_type(expression->getType(), expression->getExprLoc());
    if (!name || !value_type || !remember_function(call))
      return std::nullopt;
    llvm::json::Object reference;
    reference["declaration_id"] = declaration_id(call);
    reference["name"] = *name;
    reference["span"] = span(lambda->getSourceRange());
    llvm::json::Object result;
    result["kind"] = "function_address";
    result["function"] = std::move(reference);
    result["value_type"] = std::move(*value_type);
    result["span"] = span(expression->getSourceRange());
    if (!state_.error.empty())
      return std::nullopt;
    return Json(std::move(result));
  }

  // `&f` as a value: the address of a free function or static member
  // function of the program, which is exported so its contract can be
  // checked against the one a callee requires of the pointer.
  std::optional<Json> lower_function_address(const clang::Expr *expression,
                                             const clang::FunctionDecl *designated) {
    const auto *method = llvm::dyn_cast<clang::CXXMethodDecl>(designated);
    const clang::FunctionDecl *definition = designated->getDefinition();
    if ((method != nullptr && !method->isStatic()) || definition == nullptr ||
        is_axiom(definition) ||
        !executable_source(source_manager_.getSpellingLoc(definition->getLocation()))) {
      fail(expression->getExprLoc(),
           "a C++ function pointer value must be the address of a free or static "
           "member function defined in the selected or dependency sources");
      return std::nullopt;
    }
    auto value_type = lower_type(expression->getType(), expression->getExprLoc());
    if (!value_type || !remember_function(definition))
      return std::nullopt;
    llvm::json::Object reference;
    reference["declaration_id"] = declaration_id(definition);
    reference["name"] = method != nullptr ? method_name(method) : function_name(definition);
    reference["span"] = span(expression->getSourceRange());
    llvm::json::Object result;
    result["kind"] = "function_address";
    result["function"] = std::move(reference);
    result["value_type"] = std::move(*value_type);
    result["span"] = span(expression->getSourceRange());
    if (!state_.error.empty())
      return std::nullopt;
    return Json(std::move(result));
  }

  // `left = right` between values of an abstract type argument: its trivial
  // assignment is a store of the value read, as an integer's is.
  std::optional<Json> lower_archetype_assignment(const clang::CXXOperatorCallExpr *operation,
                                                 const clang::FunctionDecl *function) {
    const auto *method =
        llvm::dyn_cast_or_null<clang::CXXMethodDecl>(operation->getDirectCallee());
    if (method == nullptr || !method->isTrivial() ||
        !(method->isCopyAssignmentOperator() || method->isMoveAssignmentOperator()) ||
        !operation->getArg(0)->isLValue()) {
      fail(operation->getExprLoc(), "a value of an abstract type argument is only copied");
      return std::nullopt;
    }
    auto value = lower_load(archetype_place(operation->getArg(1)), operation->getArg(1)->getType(),
                            operation->getArg(1)->getSourceRange(), function);
    if (!value)
      return std::nullopt;
    llvm::json::Object result;
    const clang::Expr *left = archetype_place(operation->getArg(0));
    if (const auto *member = llvm::dyn_cast<clang::MemberExpr>(left)) {
      auto lowered = lower_member(member, function);
      if (!lowered)
        return std::nullopt;
      result["kind"] = "member_store";
      result["object"] = std::move(lowered->object);
      result["field"] = std::move(lowered->field);
    } else if (const auto *dereference = llvm::dyn_cast<clang::UnaryOperator>(left);
               dereference != nullptr && dereference->getOpcode() == clang::UO_Deref) {
      auto pointer = lower_expression(dereference->getSubExpr(), function);
      if (!pointer)
        return std::nullopt;
      result["kind"] = "store";
      result["pointer"] = std::move(*pointer);
    } else {
      auto target = lower_place_reference(left, function);
      if (!target)
        return std::nullopt;
      result["kind"] = "assign";
      result["target"] = std::move(*target);
    }
    result["value"] = std::move(*value);
    result["span"] = span(operation->getSourceRange());
    return Json(std::move(result));
  }

  // A read of the value `source`, an lvalue of `type`: a field, a
  // dereference, or a named place.
  std::optional<Json> lower_load(const clang::Expr *source, clang::QualType type,
                                 clang::SourceRange range,
                                 const clang::FunctionDecl *function) {
    auto value_type = lower_type(type.getUnqualifiedType(), range.getBegin());
    if (!value_type) {
      return std::nullopt;
    }
    llvm::json::Object result;
    if (const auto *member = llvm::dyn_cast<clang::MemberExpr>(source)) {
      auto lowered = lower_member(member, function);
      if (!lowered) {
        return std::nullopt;
      }
      result["kind"] = "member_load";
      result["object"] = std::move(lowered->object);
      result["field"] = std::move(lowered->field);
    } else if (const auto *dereference =
            llvm::dyn_cast<clang::UnaryOperator>(source);
        dereference != nullptr && dereference->getOpcode() == clang::UO_Deref) {
      auto pointer = lower_expression(dereference->getSubExpr(), function);
      if (!pointer) {
        return std::nullopt;
      }
      result["kind"] = "dereference";
      result["pointer"] = std::move(*pointer);
    } else {
      auto place = lower_place_reference(source, function);
      if (!place) {
        return std::nullopt;
      }
      result["kind"] = "load";
      result["place"] = std::move(*place);
    }
    result["value_type"] = std::move(*value_type);
    result["span"] = span(range);
    return Json(std::move(result));
  }

  // The lvalue an abstract type argument's copy reads, without the
  // qualification and materialization around it.
  const clang::Expr *archetype_place(const clang::Expr *expression) const {
    while (true) {
      expression = expression->IgnoreParens();
      if (const auto *cast = llvm::dyn_cast<clang::ImplicitCastExpr>(expression);
          cast != nullptr && cast->getCastKind() == clang::CK_NoOp) {
        expression = cast->getSubExpr();
        continue;
      }
      return expression;
    }
  }

  std::optional<Json> lower_expression(const clang::Expr *expression,
                                       const clang::FunctionDecl *function) {
    if (const auto *designated = designated_function(expression))
      return lower_function_address(expression, designated);
    if (const auto *lambda = converted_lambda(expression))
      return lower_lambda_address(expression, lambda);
    // A full expression whose temporaries end without effects, as a lambda
    // converted to a function pointer does, is its subexpression.
    if (const auto *cleanups = llvm::dyn_cast<clang::ExprWithCleanups>(expression);
        cleanups != nullptr && (!cleanups->cleanupsHaveSideEffects() ||
                                only_std_function_temporaries(cleanups->getSubExpr())))
      return lower_expression(cleanups->getSubExpr(), function);
    if (const auto *throw_expression =
            llvm::dyn_cast<clang::CXXThrowExpr>(expression)) {
      fail(throw_expression->getThrowLoc(),
           exception_behavior_ == "scalar_int32"
               ? "scalar int32 throws must be standalone statements"
               : "throw expressions are outside the normal-only C++ profile");
      return std::nullopt;
    }
    if (const auto *substitution =
            llvm::dyn_cast<clang::SubstNonTypeTemplateParmExpr>(expression)) {
      return lower_expression(substitution->getReplacement(), function);
    }
    // A defaulted integral argument, as in `s.subspan(1)`, is the constant
    // Clang evaluates for it, spanned at the call that uses it.
    if (const auto *defaulted =
            llvm::dyn_cast<clang::CXXDefaultArgExpr>(expression)) {
      const clang::Expr *value = defaulted->getExpr();
      clang::Expr::EvalResult evaluated;
      if (!value->getType()->isIntegerType() ||
          !supported_integer_type(value->getType()) ||
          !value->isCXX11ConstantExpr(context_) ||
          !value->EvaluateAsInt(evaluated, context_, clang::Expr::SE_NoSideEffects,
                                /*InConstantContext=*/true)) {
        fail(defaulted->getUsedLocation(),
             "C++ default arguments require an integral constant expression");
        return std::nullopt;
      }
      auto value_type = lower_type(defaulted->getType(), defaulted->getUsedLocation());
      if (!value_type)
        return std::nullopt;
      llvm::SmallString<32> text;
      evaluated.Val.getInt().toString(text, 10);
      llvm::json::Object result;
      result["kind"] = "compiler_constant";
      result["value"] = text.str().str();
      result["value_type"] = std::move(*value_type);
      result["span"] = span(clang::SourceRange(defaulted->getUsedLocation(),
                                               defaulted->getUsedLocation()));
      return Json(std::move(result));
    }
    if (const auto *boolean =
            llvm::dyn_cast<clang::CXXBoolLiteralExpr>(expression)) {
      return boolean_constant(boolean->getValue(), boolean->getSourceRange(),
                              false);
    }
    // Only literal null conversions are total, effect-free pointer values.
    // A nullptr_t call or variable still has evaluation behavior and is not
    // silently folded to a literal by this boundary.
    if (const auto *cast = llvm::dyn_cast<clang::CastExpr>(expression);
        cast != nullptr && cast->getCastKind() == clang::CK_NullToPointer) {
      const auto *operand = cast->getSubExpr()->IgnoreParens();
      const auto *integer = llvm::dyn_cast<clang::IntegerLiteral>(operand);
      if (!llvm::isa<clang::CXXNullPtrLiteralExpr>(operand) &&
          (integer == nullptr || !integer->getValue().isZero())) {
        fail(cast->getExprLoc(), "C++ null pointer conversion requires a literal nullptr or zero");
        return std::nullopt;
      }
      const auto *pointer = cast->getType()->getAs<clang::PointerType>();
      if ((pointer == nullptr || pointer->getPointeeType().hasQualifiers() ||
           !supported_pointer_element(pointer->getPointeeType())) &&
          record_pointer_target(cast->getType()) == nullptr) {
        fail(cast->getExprLoc(), "C++ null pointer literal requires a mutable int32 pointer, uint32 pointer, unsigned-byte pointer or simple record pointer");
        return std::nullopt;
      }
      auto value_type = lower_type(cast->getType().getUnqualifiedType(), cast->getExprLoc());
      if (!value_type)
        return std::nullopt;
      llvm::json::Object result;
      result["kind"] = "null_pointer";
      result["value_type"] = std::move(*value_type);
      result["span"] = span(cast->getSourceRange());
      return Json(std::move(result));
    }
    // Closed compile-time operations are evaluated by the pinned Clang profile,
    // and retain their source span as distinct compiler_constant artifact
    // nodes. Runtime calls are not folded or skipped by this narrow allowlist.
    const clang::Expr *candidate = expression->IgnoreParenImpCasts();
    const auto *trait =
        llvm::dyn_cast<clang::UnaryExprOrTypeTraitExpr>(candidate);
    const auto *constant_call = llvm::dyn_cast<clang::CallExpr>(candidate);
    const bool limits_max = is_numeric_limits_max_call(constant_call);
    if ((trait != nullptr && trait->getKind() == clang::UETT_SizeOf) ||
        limits_max) {
      if (expression->getType()->isIntegerType() &&
          supported_integer_type(expression->getType()) &&
          expression->isCXX11ConstantExpr(context_)) {
        clang::Expr::EvalResult evaluated;
        if (expression->EvaluateAsInt(evaluated, context_,
                                      clang::Expr::SE_NoSideEffects,
                                      /*InConstantContext=*/false)) {
          auto value_type =
              lower_type(expression->getType(), expression->getExprLoc());
          if (!value_type)
            return std::nullopt;
          llvm::SmallString<32> value;
          evaluated.Val.getInt().toString(value, 10);
          llvm::json::Object result;
          result["kind"] = "compiler_constant";
          result["value"] = value.str().str();
          result["value_type"] = std::move(*value_type);
          result["span"] = span(expression->getSourceRange());
          return Json(std::move(result));
        }
      }
      fail(expression->getExprLoc(),
           "unsupported C++ compiler constant type or evaluation");
      return std::nullopt;
    }
    if (const auto *parentheses =
            llvm::dyn_cast<clang::ParenExpr>(expression)) {
      return lower_expression(parentheses->getSubExpr(), function);
    }
    if (const auto *call = llvm::dyn_cast<clang::CallExpr>(expression)) {
      const auto *callee = call->getDirectCallee();
      if (callee != nullptr && callee->getBuiltinID() == clang::Builtin::BI__builtin_is_constant_evaluated) {
        if (call->getNumArgs() != 0 || !call->getType()->isBooleanType()) {
          fail(call->getExprLoc(), "unsupported C++ runtime constant-evaluation primitive signature");
          return std::nullopt;
        }
        auto value_type = lower_type(call->getType(), call->getExprLoc());
        if (!value_type) return std::nullopt;
        llvm::json::Object result;
        result["kind"] = "runtime_constant_evaluation";
        result["value_type"] = std::move(*value_type);
        result["span"] = span(call->getSourceRange());
        return Json(std::move(result));
      }
      if (callee == nullptr || callee->getBuiltinID() != 0 ||
          callee->getReturnType()->isReferenceType() || callee->getReturnType()->isVoidType()) {
        fail(call->getExprLoc(), "C++ expression observers require a direct scalar value call; compiler builtins and reference results remain unsupported");
        return std::nullopt;
      }
      auto operation = lower_call_operation(call, function, true);
      auto value_type = lower_type(call->getType(), call->getExprLoc());
      if (!operation || !value_type) return std::nullopt;
      llvm::json::Object result;
      result["kind"] = "observer_call";
      result["callee"] = std::move(operation->callee);
      result["arguments"] = std::move(operation->arguments);
      result["value_type"] = std::move(*value_type);
      result["span"] = std::move(operation->span);
      return Json(std::move(result));
    }
    if (const auto *list = llvm::dyn_cast<clang::InitListExpr>(expression)) {
      // Retain the semantic conversion checked by Clang; substituting a
      // modulo cast of the written initializer would admit C++ narrowing.
      const auto *value = scalar_list_initializer(list);
      if (value == nullptr) {
        fail(list->getExprLoc(),
             "supported C++ scalar brace initialization requires one "
             "Clang-resolved integer or Boolean initializer");
        return std::nullopt;
      }
      return lower_expression(value, function);
    }
    if (const auto *cast =
            llvm::dyn_cast<clang::ExplicitCastExpr>(expression)) {
      if (supported_byte_pointer_cast(cast)) {
        auto value = lower_expression(cast->getSubExpr(), function);
        auto value_type = lower_type(cast->getType().getUnqualifiedType(), cast->getExprLoc());
        if (!value || !value_type) return std::nullopt;
        llvm::json::Object result;
        result["kind"] = "byte_pointer_cast";
        result["value"] = std::move(*value);
        result["value_type"] = std::move(*value_type);
        result["span"] = span(cast->getSourceRange());
        return Json(std::move(result));
      }
      if (cast->getType()->isEnumeralType() || cast->getSubExpr()->getType()->isEnumeralType()) {
        if (cast->getCastKind() != clang::CK_IntegralCast &&
            cast->getCastKind() != clang::CK_IntegralToBoolean &&
            cast->getCastKind() != clang::CK_NoOp) {
          fail(cast->getExprLoc(), "unsupported explicit C++ enum conversion");
          return std::nullopt;
        }
        auto value = lower_expression(cast->getSubExpr(), function);
        auto value_type = lower_type(cast->getType().getUnqualifiedType(), cast->getExprLoc());
        if (!value || !value_type) return std::nullopt;
        llvm::json::Object result;
        result["kind"] = "enum_cast";
        result["value"] = std::move(*value);
        result["value_type"] = std::move(*value_type);
        result["span"] = span(cast->getSourceRange());
        return Json(std::move(result));
      }
      if (cast->getCastKind() == clang::CK_NoOp &&
          context_.hasSameType(cast->getType(),
                               cast->getSubExpr()->getType()) &&
          (cast->getType()->isBooleanType() || cast->getType()->isPointerType() ||
           (cast->getType()->isIntegerType() &&
            supported_integer_type(cast->getType())))) {
        return lower_expression(cast->getSubExpr(), function);
      }
      if (cast->getCastKind() != clang::CK_IntegralCast &&
          cast->getCastKind() != clang::CK_IntegralToBoolean &&
          cast->getCastKind() != clang::CK_BooleanToSignedIntegral) {
        fail(cast->getExprLoc(), "unsupported explicit C++ conversion");
        return std::nullopt;
      }
      auto value = lower_expression(cast->getSubExpr(), function);
      auto value_type = lower_type(cast->getType().getUnqualifiedType(), cast->getExprLoc());
      if (!value || !value_type)
        return std::nullopt;
      llvm::json::Object result;
      result["kind"] = "integral_cast";
      result["value"] = std::move(*value);
      result["value_type"] = std::move(*value_type);
      result["span"] = span(cast->getSourceRange());
      return Json(std::move(result));
    }
    if (const auto *unary = llvm::dyn_cast<clang::UnaryOperator>(expression);
        unary != nullptr && unary->getOpcode() == clang::UO_LNot) {
      auto value = lower_expression(unary->getSubExpr(), function);
      auto value_type = lower_type(unary->getType(), unary->getExprLoc());
      if (!value || !value_type || !unary->getSubExpr()->getType()->isIntegerType()) {
        fail(unary->getExprLoc(), "C++ logical negation requires a supported integral operand");
        return std::nullopt;
      }
      llvm::json::Object result;
      result["kind"] = "logical_not";
      result["value"] = std::move(*value);
      result["value_type"] = std::move(*value_type);
      result["span"] = span(unary->getSourceRange());
      return Json(std::move(result));
    }
    if (const auto *unary = llvm::dyn_cast<clang::UnaryOperator>(expression);
        unary != nullptr && unary->getOpcode() == clang::UO_Minus) {
      if (context_.getTypeSize(unary->getType()) == 128) {
        fail(unary->getOperatorLoc(), "C++ wide negation is not supported");
        return std::nullopt;
      }
      auto value = lower_expression(unary->getSubExpr(), function);
      auto value_type = lower_type(unary->getType(), unary->getExprLoc());
      auto zero_type = lower_type(unary->getType(), unary->getExprLoc());
      if (!value || !value_type || !zero_type ||
          !unary->getType()->isIntegerType())
        return std::nullopt;
      llvm::json::Object zero;
      zero["kind"] = "integer_literal";
      zero["value"] = "0";
      zero["value_type"] = std::move(*zero_type);
      zero["span"] = span(unary->getSourceRange());
      llvm::json::Object result;
      result["kind"] = "binary";
      result["operator"] = "subtract";
      result["left"] = std::move(zero);
      result["right"] = std::move(*value);
      result["value_type"] = std::move(*value_type);
      result["span"] = span(unary->getSourceRange());
      return Json(std::move(result));
    }
    if (const auto *cast =
            llvm::dyn_cast<clang::ImplicitCastExpr>(expression)) {
      if (cast->getCastKind() == clang::CK_IntegralCast ||
          cast->getCastKind() == clang::CK_IntegralToBoolean ||
          cast->getCastKind() == clang::CK_BooleanToSignedIntegral) {
        auto value = lower_expression(cast->getSubExpr(), function);
        auto value_type = lower_type(cast->getType().getUnqualifiedType(), cast->getExprLoc());
        if (!value || !value_type) {
          return std::nullopt;
        }
        llvm::json::Object result;
        result["kind"] = "integral_cast";
        result["value"] = std::move(*value);
        result["value_type"] = std::move(*value_type);
        result["span"] = span(cast->getSourceRange());
        return Json(std::move(result));
      }
      if (cast->getCastKind() != clang::CK_LValueToRValue) {
        fail(cast->getExprLoc(),
             "unsupported implicit conversion in the first C++ slice");
        return std::nullopt;
      }
      const clang::Expr *source = cast->getSubExpr()->IgnoreParens();
      if (const auto *reference = llvm::dyn_cast<clang::DeclRefExpr>(source);
          reference != nullptr &&
          llvm::isa<clang::VarDecl>(reference->getDecl()) &&
          !llvm::isa<clang::ParmVarDecl>(reference->getDecl()) &&
          llvm::cast<clang::VarDecl>(reference->getDecl())->hasGlobalStorage()) {
        return lower_constant_reference(reference, cast);
      }
      return lower_load(source, cast->getType(), cast->getSourceRange(), function);
    }
    // A copy of an abstract type argument's value is a load of it, as an
    // integer's is.
    if (const auto *construction = llvm::dyn_cast<clang::CXXConstructExpr>(expression);
        construction != nullptr && archetype_name(construction->getType()) != nullptr) {
      const clang::CXXConstructorDecl *constructor = construction->getConstructor();
      if (construction->getNumArgs() != 1 || !constructor->isTrivial() ||
          !(constructor->isCopyConstructor() || constructor->isMoveConstructor())) {
        fail(construction->getExprLoc(),
             "a value of an abstract type argument is only copied");
        return std::nullopt;
      }
      return lower_load(archetype_place(construction->getArg(0)), construction->getType(),
                        construction->getSourceRange(), function);
    }
    if (const auto *materialized = llvm::dyn_cast<clang::MaterializeTemporaryExpr>(expression);
        materialized != nullptr && archetype_name(materialized->getType()) != nullptr)
      return lower_expression(materialized->getSubExpr(), function);
    if (const auto *address = llvm::dyn_cast<clang::UnaryOperator>(expression);
        address != nullptr && address->getOpcode() == clang::UO_AddrOf) {
      const clang::Expr *operand = address->getSubExpr()->IgnoreParenImpCasts();
      const auto *reference = llvm::dyn_cast<clang::DeclRefExpr>(operand);
      const auto *parameter =
          reference == nullptr
              ? nullptr
              : llvm::dyn_cast<clang::VarDecl>(reference->getDecl());
      const auto *reference_type =
          parameter == nullptr
              ? nullptr
              : parameter->getType()->getAs<clang::LValueReferenceType>();
      const bool integer_field = llvm::isa<clang::MemberExpr>(operand) &&
          operand->isLValue() && supported_pointer_element(operand->getType());
      const bool automatic_scalar = parameter != nullptr &&
          parameter->hasLocalStorage() &&
          supported_pointer_element(parameter->getType());
      const bool integer_reference = reference_type != nullptr &&
          context_.hasSameType(reference_type->getPointeeType().getUnqualifiedType(),
                               context_.IntTy);
      if (!integer_field && (parameter == nullptr || parameter->getDeclContext() != function ||
          (!automatic_scalar && !integer_reference))) {
        fail(address->getOperatorLoc(),
             "supported C++ address-of must name a native scalar object or int reference in the current function");
        return std::nullopt;
      }
      auto place = lower_place_reference(operand, function);
      auto value_type = lower_type(address->getType(), address->getExprLoc());
      if (!place || !value_type) {
        return std::nullopt;
      }
      llvm::json::Object result;
      result["kind"] = "address_of";
      result["place"] = std::move(*place);
      result["value_type"] = std::move(*value_type);
      result["span"] = span(address->getSourceRange());
      return Json(std::move(result));
    }
    if (const auto *literal =
            llvm::dyn_cast<clang::IntegerLiteral>(expression)) {
      auto value_type = lower_type(literal->getType(), literal->getExprLoc());
      if (!value_type) {
        return std::nullopt;
      }
      llvm::SmallString<32> value;
      literal->getValue().toString(value, 10,
                                   literal->getType()->isSignedIntegerType());
      llvm::json::Object result;
      result["kind"] = "integer_literal";
      result["value"] = value.str().str();
      result["value_type"] = std::move(*value_type);
      result["span"] = span(literal->getSourceRange());
      return Json(std::move(result));
    }
    if (const auto *binary =
            llvm::dyn_cast<clang::BinaryOperator>(expression)) {
      if (binary->getOpcode() != clang::BO_Add &&
          binary->getOpcode() != clang::BO_Sub &&
          binary->getOpcode() != clang::BO_Div &&
          binary->getOpcode() != clang::BO_Rem &&
          binary->getOpcode() != clang::BO_LT &&
          binary->getOpcode() != clang::BO_GT &&
          binary->getOpcode() != clang::BO_EQ &&
          binary->getOpcode() != clang::BO_NE &&
          binary->getOpcode() != clang::BO_Mul &&
          binary->getOpcode() != clang::BO_LE &&
          binary->getOpcode() != clang::BO_GE &&
          binary->getOpcode() != clang::BO_LAnd) {
        fail(binary->getOperatorLoc(),
             "unsupported binary operator; this C++ slice supports "
             "signed/unsigned "
             "32/64-bit arithmetic (+, -, *, /, %), same-width signed "
             "comparisons, and built-in bool && bool only");
        return std::nullopt;
      }
      const auto operand_type = binary->getLHS()->getType();
      const bool wide = operand_type->isIntegerType() &&
                        context_.getTypeSize(operand_type) == 128;
      const bool signed_wide_product = wide &&
          binary->getOpcode() == clang::BO_Mul &&
          binary->getType()->isSignedIntegerType();
      const bool wide_division = wide &&
          (binary->getOpcode() == clang::BO_Div ||
           binary->getOpcode() == clang::BO_Rem);
      const bool supported_wide_arithmetic = signed_wide_product || wide_division;
      const bool wide_comparison = wide &&
          (binary->getOpcode() == clang::BO_EQ || binary->getOpcode() == clang::BO_NE ||
           binary->getOpcode() == clang::BO_LT ||
           binary->getOpcode() == clang::BO_GT || binary->getOpcode() == clang::BO_LE ||
           binary->getOpcode() == clang::BO_GE);
      if (wide && !supported_wide_arithmetic && !wide_comparison) {
        fail(binary->getOperatorLoc(),
             "C++ wide arithmetic supports checked signed multiplication and signed/unsigned division/remainder only; wide comparisons support ==, !=, <, >, <=, >=");
        return std::nullopt;
      }
      const bool pointer_offset =
          binary->getType()->isPointerType() &&
          ((binary->getOpcode() == clang::BO_Add &&
            (binary->getLHS()->getType()->isPointerType() ||
             binary->getRHS()->getType()->isPointerType())) ||
           (binary->getOpcode() == clang::BO_Sub &&
            binary->getLHS()->getType()->isPointerType() &&
            binary->getRHS()->getType()->isIntegerType()));
      if (binary->getOpcode() == clang::BO_Sub &&
          binary->getLHS()->getType()->isPointerType() &&
          binary->getRHS()->getType()->isPointerType()) {
        fail(binary->getOperatorLoc(),
             "C++ pointer arithmetic does not support pointer differences");
        return std::nullopt;
      }
      if (binary->getOpcode() == clang::BO_Add ||
          binary->getOpcode() == clang::BO_Sub ||
          binary->getOpcode() == clang::BO_Mul ||
          binary->getOpcode() == clang::BO_Div ||
          binary->getOpcode() == clang::BO_Rem) {
        if (!pointer_offset &&
            (!binary->getType()->isIntegerType() ||
             (context_.getTypeSize(binary->getType()) != 32 &&
              context_.getTypeSize(binary->getType()) != 64 &&
              !supported_wide_arithmetic))) {
          fail(binary->getOperatorLoc(),
               "C++ arithmetic requires signed/unsigned 32/64-bit operands or "
               "native object pointer addition with a 32/64-bit index or subtraction "
               "with an int32 index; pointer differences remain unsupported");
          return std::nullopt;
        }
      }
      auto left = lower_expression(binary->getLHS(), function);
      auto right = lower_expression(binary->getRHS(), function);
      auto value_type = lower_type(binary->getType(), binary->getExprLoc());
      if (!left || !right || !value_type) {
        return std::nullopt;
      }
      llvm::json::Object result;
      result["kind"] = "binary";
      if (binary->getOpcode() == clang::BO_Add) {
        result["operator"] = "add";
      } else if (binary->getOpcode() == clang::BO_Sub) {
        result["operator"] = "subtract";
      } else if (binary->getOpcode() == clang::BO_Div) {
        result["operator"] = "divide";
      } else if (binary->getOpcode() == clang::BO_Rem) {
        result["operator"] = "remainder";
      } else if (binary->getOpcode() == clang::BO_LT) {
        result["operator"] = "less_than";
      } else if (binary->getOpcode() == clang::BO_GT) {
        result["operator"] = "greater_than";
      } else if (binary->getOpcode() == clang::BO_EQ) {
        result["operator"] = "equal";
      } else if (binary->getOpcode() == clang::BO_NE) {
        result["operator"] = "not_equal";
      } else if (binary->getOpcode() == clang::BO_Mul) {
        result["operator"] = "multiply";
      } else if (binary->getOpcode() == clang::BO_LE) {
        result["operator"] = "less_equal";
      } else if (binary->getOpcode() == clang::BO_LAnd) {
        result["operator"] = "logical_and";
      } else {
        result["operator"] = "greater_equal";
      }
      result["left"] = std::move(*left);
      result["right"] = std::move(*right);
      result["value_type"] = std::move(*value_type);
      result["span"] = span(binary->getSourceRange());
      return Json(std::move(result));
    }
    fail(expression->getExprLoc(),
         "unsupported expression in the first C++ slice");
    return std::nullopt;
  }

  bool remember_record(const clang::CXXRecordDecl *record) {
    // An abstract type argument is a type parameter, not a record of the
    // artifact: a value of it is passed and copied as a word.
    if (record != nullptr && archetype_name(context_.getRecordType(record)) != nullptr)
      return true;
    const clang::CXXRecordDecl *definition =
        record == nullptr ? nullptr : record->getDefinition();
    if (definition == nullptr) {
      fail({}, "the supported C++ record type must be complete");
      return false;
    }
    if (context_.getLangOpts().CXXExceptions &&
        exception_behavior_ != "scalar_int32" &&
        !definition->hasTrivialDestructor()) {
      fail(definition->getLocation(),
           "the exception-enabled C++ profile is limited to an object-free "
           "normal-only graph");
      return false;
    }
    const clang::CXXRecordDecl *canonical = definition->getCanonicalDecl();
    if (known_records_.insert(canonical).second) {
      if (known_records_.size() > kMaxRecordDeclarations) {
        fail(definition->getLocation(), "C++ artifact budget exhausted: record declarations (limit " +
                 std::to_string(kMaxRecordDeclarations) + ")");
        return false;
      }
      if (!validate_record(definition)) {
        return false;
      }
      record_definitions_.push_back(definition);
    }
    return true;
  }

  static bool needs_destructor_body(const clang::CXXDestructorDecl *destructor) {
    // Clang proves an in-class defaulted trivial destructor has no effects.
    // Deleted and other explicitly written declarations retain their checks.
    return destructor != nullptr && !destructor->isImplicit() &&
           !(destructor->isDefaulted() && !destructor->isDeleted() &&
             destructor->isTrivial()) &&
           !no_op_virtual_destructor(destructor->getParent());
  }

  // A polymorphic class whose destruction does nothing but reset the
  // vtable pointer, which the compiler does and no proof reads: its
  // destructor is implicit, defaulted, or has an empty body, and what runs
  // after it does nothing either. Clang's access checks decide who may
  // destroy it, so a protected base destructor is one too.
  static bool no_op_virtual_destructor(const clang::CXXRecordDecl *record) {
    record = record == nullptr ? nullptr : record->getDefinition();
    if (record == nullptr || !record->isPolymorphic() ||
        record->hasTrivialDestructor())
      return false;
    if (const clang::CXXDestructorDecl *destructor = record->getDestructor()) {
      if (destructor->isDeleted())
        return false;
      if (!destructor->isImplicit() && !destructor->isDefaulted()) {
        const auto *definition = llvm::dyn_cast_or_null<clang::CXXDestructorDecl>(
            destructor->getDefinition());
        const auto *body = definition == nullptr
                               ? nullptr
                               : llvm::dyn_cast_or_null<clang::CompoundStmt>(
                                     definition->getBody());
        if (body == nullptr || !body->body_empty())
          return false;
      }
    }
    return destruction_after_body_is_no_op(record);
  }

  // The written destructor of a polymorphic class's base, which a derived
  // class's destructor runs after its own body on the base subobject: the
  // base has no base of its own and fields with trivial destruction.
  static const clang::CXXDestructorDecl *
  effectful_base_destructor(const clang::CXXRecordDecl *record) {
    if (record == nullptr || record->getNumBases() != 1) return nullptr;
    const auto *base = record->bases_begin()->getType()->getAsCXXRecordDecl();
    base = base == nullptr ? nullptr : base->getDefinition();
    if (base == nullptr || !base->isPolymorphic() || base->getNumBases() != 0 ||
        base->hasTrivialDestructor() || no_op_virtual_destructor(base))
      return nullptr;
    const clang::CXXDestructorDecl *destructor = base->getDestructor();
    if (!needs_destructor_body(destructor) || !fields_have_trivial_destruction(base))
      return nullptr;
    return destructor;
  }

  static bool fields_have_trivial_destruction(const clang::CXXRecordDecl *record) {
    for (const clang::FieldDecl *field : record->fields()) {
      const auto *field_record = field->getType()->getAsCXXRecordDecl();
      if (field_record != nullptr && field_record->getDefinition() != nullptr &&
          !field_record->getDefinition()->hasTrivialDestructor())
        return false;
    }
    return true;
  }

  // What a class's destruction runs after its destructor's body: its
  // fields' destructors, then its base's. Neither may run code a proof
  // sees, since base destruction is not executed.
  static bool destruction_after_body_is_no_op(const clang::CXXRecordDecl *record) {
    for (const clang::FieldDecl *field : record->fields()) {
      const auto *field_record = field->getType()->getAsCXXRecordDecl();
      if (field_record != nullptr && field_record->getDefinition() != nullptr &&
          !field_record->getDefinition()->hasTrivialDestructor())
        return false;
    }
    for (const clang::CXXBaseSpecifier &base : record->bases()) {
      const auto *base_record = base.getType()->getAsCXXRecordDecl();
      if (base_record == nullptr || base_record->getDefinition() == nullptr ||
          (!base_record->getDefinition()->hasTrivialDestructor() &&
           !no_op_virtual_destructor(base_record)))
        return false;
    }
    return true;
  }

  bool validate_record(const clang::CXXRecordDecl *record) {
    if (llvm::isa<clang::ClassTemplateSpecializationDecl>(record)) {
      record_name(record);
      if (!state_.error.empty())
        return false;
    }
    if ((!record->isStruct() && !record->isClass()) || record->getName().empty()) {
      fail(record->getLocation(),
           "the supported C++ record must be a named struct or class");
      return false;
    }
    if (!is_in_logical_source(record->getLocation()) &&
        !dependency_source(record->getLocation())) {
      fail(record->getLocation(),
           "the supported C++ record must be declared within the import root");
      return false;
    }
    if (record->isPolymorphic())
      return validate_polymorphic_record(record);
    if (record->getNumBases() != 0) {
      if (record->getNumBases() != 1 || !record->field_empty()) {
        fail(record->getLocation(),
             "the supported C++ base profile requires one public non-virtual base and no own fields");
        return false;
      }
      const auto &base = *record->bases_begin();
      if (base.isVirtual() || base.getAccessSpecifier() != clang::AS_public ||
          !record->isTriviallyCopyable() || !record->hasTrivialDestructor()) {
        fail(record->getLocation(),
             "the supported C++ base profile requires public non-virtual inheritance and trivial copying/destruction");
        return false;
      }
      const auto *base_record = base.getType()->getAsCXXRecordDecl();
      if (base_record == nullptr || !remember_record(base_record) ||
          !base_record->getDefinition()->hasTrivialDestructor()) {
        if (state_.error.empty())
          fail(base.getBeginLoc(), "C++ base subobjects require trivial destruction");
        return false;
      }
      const auto &layout = context_.getASTRecordLayout(record);
      const auto &base_layout = context_.getASTRecordLayout(base_record);
      if (!layout.getBaseClassOffset(base_record).isZero() ||
          layout.getSize() != base_layout.getSize() ||
          layout.getAlignment() != base_layout.getAlignment()) {
        fail(base.getBeginLoc(), "C++ single-base layout must preserve the complete base layout");
        return false;
      }
    }
    if (!record->isStandardLayout()) {
      fail(record->getLocation(), "the supported C++ record must be standard-layout");
      return false;
    }
    bool has_state = false;
    for (const clang::FieldDecl *field : record->fields())
      has_state = has_state || !stateless_field(field);
    // `field_empty` is kept as the first test: it is what refuses a record
    // Clang has not completed, as it did before stateless members existed.
    if ((record->field_empty() || !has_state) && record->getNumBases() == 0) {
      fail(record->getLocation(),
           "the supported C++ record must contain at least one field");
      return false;
    }
    const clang::CXXDestructorDecl *supported_destructor =
        record->getDestructor();
    if (needs_destructor_body(supported_destructor)) {
      if (!validate_destructor(supported_destructor, record))
        return false;
    } else if (!record->isTriviallyCopyable() ||
               !record->hasTrivialDestructor()) {
      fail(record->getLocation(),
           "a record without a supported destructor must remain trivially copyable with trivial destruction");
      return false;
    }
    return validate_record_fields(record);
  }

  // A polymorphic class: its object starts with the vtable pointer Clang
  // lays out, which no field names and no contract reads. It has at most
  // one public non-virtual base, itself polymorphic, at offset zero; its own
  // fields follow the whole base. Nothing copies it: it is reached through a
  // reference or built in a local by its constructor, and its destruction
  // runs at most its own destructor's body.
  bool validate_polymorphic_record(const clang::CXXRecordDecl *record) {
    if (record->getNumVBases() != 0 || record->getNumBases() > 1) {
      fail(record->getLocation(),
           "a polymorphic C++ class has at most one public non-virtual base");
      return false;
    }
    const clang::CXXDestructorDecl *destructor = record->getDestructor();
    // A destructor that runs code is the class's own, written here, and
    // checked as any is; what runs after its body, the fields' and the
    // base's destruction, does nothing. A local's destructor is called
    // directly, so whether it is virtual does not change the call.
    // A base destructor that runs code runs after the class's own written
    // destructor, which may then be empty; the class's fields still have
    // trivial destruction.
    if (!record->hasTrivialDestructor() && !no_op_virtual_destructor(record)) {
      const bool base_runs = effectful_base_destructor(record) != nullptr;
      if (!needs_destructor_body(destructor) ||
          !(destruction_after_body_is_no_op(record) ||
            (base_runs && fields_have_trivial_destruction(record)))) {
        fail(record->getLocation(),
             "a polymorphic C++ class's destructor is written in the class and "
             "runs after it only its base's written destructor or nothing: its "
             "fields have trivial destruction");
        return false;
      }
      if (!validate_destructor(destructor, record, base_runs))
        return false;
    }
    const auto &layout = context_.getASTRecordLayout(record);
    if (record->getNumBases() == 1) {
      const auto &base = *record->bases_begin();
      const auto *base_record = base.getType()->getAsCXXRecordDecl();
      if (base.isVirtual() || base.getAccessSpecifier() != clang::AS_public ||
          base_record == nullptr || !remember_record(base_record) ||
          !base_record->getDefinition()->isPolymorphic()) {
        if (state_.error.empty())
          fail(base.getBeginLoc(),
               "a polymorphic C++ class's base is public, non-virtual, and polymorphic");
        return false;
      }
      const auto *definition = base_record->getDefinition();
      const auto base_size = context_.getASTRecordLayout(definition).getSize();
      unsigned index = 0;
      bool tail_reuse = false;
      for (const clang::FieldDecl *field : record->fields()) {
        (void)field;
        tail_reuse = tail_reuse ||
            context_.toCharUnitsFromBits(layout.getFieldOffset(index)) < base_size;
        ++index;
      }
      if (!layout.getBaseClassOffset(definition).isZero() || tail_reuse) {
        fail(base.getBeginLoc(),
             "a polymorphic C++ class's base is at offset zero, and its own fields follow the "
             "whole base");
        return false;
      }
    }
    return validate_record_fields(record);
  }

  bool validate_record_fields(const clang::CXXRecordDecl *record) {
    for (const clang::FieldDecl *field : record->fields()) {
      if (stateless_field(field))
        continue;
      // A class template instance's default member initializer, which Clang
      // instantiates only where a construction uses it.
      if (field->hasInClassInitializer() && field->getInClassInitializer() == nullptr &&
          compiler_.getSema()
              .BuildCXXDefaultInitExpr(field->getLocation(),
                                       const_cast<clang::FieldDecl *>(field))
              .isInvalid()) {
        fail(field->getLocation(), "a C++ default member initializer cannot be instantiated");
        return false;
      }
      const clang::QualType type = field->getType();
      // A field of a generic template's abstract type argument holds a
      // value of that type, which the body only copies.
      if (archetype_name(type) != nullptr && !type.hasQualifiers() &&
          !field->isBitField() && !field->isMutable() && !field->hasInClassInitializer())
        continue;
      const auto *pointer = type->getAs<clang::PointerType>();
      const bool mutable_int =
          !type.hasQualifiers() &&
          (supported_byte_enum(type) ||
           (type->isIntegerType() && !type->isBooleanType() &&
            (context_.hasSameType(type.getUnqualifiedType(), context_.UnsignedCharTy) ||
             context_.getTypeSize(type) == 32 || context_.getTypeSize(type) == 64)));
      // The pointer field itself is mutable; its native element may be
      // const, as in `std::span<const int>`'s data pointer.
      const bool mutable_int_pointer =
          pointer != nullptr && !type.hasQualifiers() &&
          supported_pointer_element(pointer->getPointeeType());
      const auto *array = context_.getAsConstantArrayType(type);
      const bool native_array = array != nullptr && !type.hasQualifiers() &&
          !array->getElementType().hasQualifiers() &&
          supported_pointer_element(array->getElementType()) &&
          !array->getSize().isZero() &&
          array->getSize().getZExtValue() <= std::numeric_limits<std::uint32_t>::max();
      const auto *embedded = type->getAsCXXRecordDecl();
      const bool mutable_record = embedded != nullptr && !type.hasQualifiers();
      const auto *pointed_record = record_pointer_target(type);
      // Access control is checked by Clang at each source use. It does not
      // change the layout or memory authority of a resolved data field.
      if (field->isBitField() ||
          field->isMutable() ||
          (field->hasInClassInitializer() && !constant_member_initializer(field)) ||
          field->getName().empty() ||
          (!mutable_int && !mutable_int_pointer && !mutable_record && !native_array &&
           pointed_record == nullptr)) {
        fail(
            field->getLocation(),
            "the supported C++ record fields must be named mutable 32/64-bit "
            "integers, unsigned char, mutable pointers to or nonempty arrays of native int/unsigned int/unsigned char/std::byte elements, mutable pointers to simple records, or embedded record fields without bit-fields");
        return false;
      }
      if (pointed_record != nullptr && !remember_record(pointed_record))
        return false;
      if (mutable_record) {
        if (!remember_record(embedded))
          return false;
        if (!embedded->getDefinition()->hasTrivialDestructor()) {
          fail(field->getLocation(),
               "embedded C++ record fields require trivial destruction");
          return false;
        }
      }
    }
    return true;
  }

  // Whether `statement` reads `this`, directly or through an implicit
  // member access.
  static bool reads_this(const clang::Stmt *statement) {
    if (statement == nullptr) return false;
    if (llvm::isa<clang::CXXThisExpr>(statement)) return true;
    for (const clang::Stmt *child : statement->children()) {
      if (reads_this(child)) return true;
    }
    return false;
  }

  bool validate_constructor(const clang::CXXConstructorDecl *constructor,
                            const clang::CXXRecordDecl *record) {
    // A polymorphic class's construction also sets its vtable pointer,
    // which no field names and no proof reads. Its one base may be a
    // polymorphic class with no fields and no constructor of its own,
    // whose implicit default construction only sets that pointer. While
    // either constructs, the object's dynamic type is still changing, so
    // nothing reads `this`: the members initialize from the parameters and
    // the body is empty.
    const clang::CXXRecordDecl *empty_base = nullptr;
    if (record->getNumBases() != 0) {
      const clang::CXXBaseSpecifier &specifier = *record->bases_begin();
      const auto *base = specifier.getType()->getAsCXXRecordDecl();
      if (!record->isPolymorphic() || record->getNumBases() != 1 ||
          specifier.isVirtual() || base == nullptr || !base->isPolymorphic() ||
          base->getNumBases() != 0) {
        fail(constructor->getLocation(),
             "C++ constructors with base subobjects remain unsupported, except "
             "a polymorphic class's polymorphic base with no base of its own");
        return false;
      }
      // A base with a constructor of its own is built by naming it in the
      // initializer list; one without is field-less, and its implicit
      // construction only sets the vtable pointer.
      const clang::CXXCtorInitializer *base_initializer = nullptr;
      for (const clang::CXXCtorInitializer *initializer : constructor->inits())
        if (initializer->isBaseInitializer()) base_initializer = initializer;
      const auto *construction =
          base_initializer == nullptr
              ? nullptr
              : llvm::dyn_cast<clang::CXXConstructExpr>(
                    base_initializer->getInit()->IgnoreParenImpCasts());
      const bool constructed =
          base->hasUserDeclaredConstructor() && base_initializer != nullptr &&
          base_initializer->isWritten() && construction != nullptr &&
          construction->getConstructor() != nullptr &&
          construction->getConstructor()->getParent()->getCanonicalDecl() ==
              base->getCanonicalDecl() &&
          !construction->getConstructor()->isDefaultConstructor();
      const bool implicit_empty = !base->hasUserDeclaredConstructor() &&
                                  base->field_empty() &&
                                  (base_initializer == nullptr ||
                                   !base_initializer->isWritten());
      if (!constructed && !implicit_empty) {
        fail(constructor->getLocation(),
             "a polymorphic C++ class's constructor names its base's own "
             "non-default constructor in its initializer list, or its base has "
             "no fields and no constructor of its own");
        return false;
      }
      empty_base = base->getCanonicalDecl();
    }
    if (record->isPolymorphic()) {
      const auto *body =
          llvm::dyn_cast_or_null<clang::CompoundStmt>(constructor->getBody());
      bool reads = body == nullptr || !body->body_empty();
      for (const clang::CXXCtorInitializer *initializer : constructor->inits()) {
        reads = reads || ((initializer->isMemberInitializer() ||
                           initializer->isBaseInitializer()) &&
                          reads_this(initializer->getInit()));
      }
      if (reads) {
        fail(constructor->getLocation(),
             "a polymorphic C++ constructor initializes its members without "
             "reading `this` and has an empty body: the object's dynamic type "
             "changes while it constructs");
        return false;
      }
    }
    const auto *prototype =
        constructor->getType()->getAs<clang::FunctionProtoType>();
    if (constructor->getAccess() != clang::AS_public ||
        constructor->isDefaultConstructor() ||
        constructor->isCopyOrMoveConstructor() ||
        constructor->isDelegatingConstructor() || constructor->isVariadic() ||
        prototype == nullptr || !prototype->isNothrow()) {
      fail(constructor->getLocation(),
           "the supported constructor must be one public non-default noexcept constructor without copying, moving, delegation, or variadic arguments");
      return false;
    }
    if (!constructor->doesThisDeclarationHaveABody() ||
        constructor->getDefinition() != constructor ||
        !executable_source(constructor->getLocation())) {
      fail(constructor->getLocation(),
           "the supported constructor must have a definition in the selected file or a declared dependency");
      return false;
    }
    for (const clang::ParmVarDecl *parameter : constructor->parameters()) {
      if (parameter->hasDefaultArg()) {
        fail(parameter->getLocation(),
             "default constructor arguments are outside the supported slice");
        return false;
      }
    }

    const unsigned field_count =
        std::distance(record->field_begin(), record->field_end());
    if (has_stateless_field(record)) {
      fail(constructor->getLocation(),
           "supported constructors require records without stateless members");
      return false;
    }
    if (constructor->getNumCtorInitializers() !=
        field_count + (empty_base == nullptr ? 0 : 1)) {
      fail(constructor->getLocation(),
           "the supported constructor must explicitly initialize every field in declaration order");
      return false;
    }
    std::vector<const clang::CXXCtorInitializer *> source_order(field_count,
                                                                nullptr);
    // A written base initializer comes first, as it runs first.
    unsigned members_from = 0;
    for (const clang::CXXCtorInitializer *initializer : constructor->inits()) {
      if (initializer->isBaseInitializer() && initializer->isWritten()) {
        if (initializer->getSourceOrder() != 0) {
          fail(initializer->getSourceLocation(),
               "the supported constructor names its base's construction first");
          return false;
        }
        members_from = 1;
      }
    }
    for (const clang::CXXCtorInitializer *initializer : constructor->inits()) {
      // The base's construction, which the body emits first.
      if (empty_base != nullptr && initializer->isBaseInitializer() &&
          initializer->getBaseClass()->getAsCXXRecordDecl()->getCanonicalDecl() ==
              empty_base) {
        continue;
      }
      const unsigned order = initializer->isWritten()
                                 ? initializer->getSourceOrder() - members_from
                                 : field_count;
      if (!initializer->isWritten() || !initializer->isMemberInitializer() ||
          order >= field_count || source_order[order] != nullptr) {
        fail(constructor->getLocation(),
             "the supported constructor must use one written member initializer per field");
        return false;
      }
      source_order[order] = initializer;
    }
    unsigned index = 0;
    for (const clang::FieldDecl *field : record->fields()) {
      if (source_order[index] == nullptr ||
          source_order[index]->getMember() != field) {
        fail(source_order[index] == nullptr
                 ? constructor->getLocation()
                 : source_order[index]->getSourceLocation(),
             "the supported constructor member initializer list must follow declaration order");
        return false;
      }
      ++index;
    }
    return true;
  }

  bool validate_destructor(const clang::CXXDestructorDecl *destructor,
                           const clang::CXXRecordDecl *record,
                           bool empty_body_allowed = false) {
    const auto *prototype =
        destructor->getType()->getAs<clang::FunctionProtoType>();
    if (destructor->getParent()->getCanonicalDecl() !=
            record->getCanonicalDecl() ||
        destructor->getAccess() != clang::AS_public ||
        (destructor->isVirtual() && !record->isPolymorphic()) ||
        destructor->isDeleted() ||
        prototype == nullptr || !prototype->isNothrow() ||
        prototype->getExceptionSpecType() != clang::EST_BasicNoexcept ||
        !destructor->getExceptionSpecSourceRange().isValid()) {
      fail(destructor->getLocation(),
           "the supported destructor must be public, non-virtual outside a polymorphic class, non-deleted, and explicitly noexcept");
      return false;
    }
    if (!destructor->doesThisDeclarationHaveABody() ||
        destructor->getDefinition() != destructor ||
        !is_in_logical_source(destructor->getLocation())) {
      fail(destructor->getLocation(),
           "the supported destructor must have an inline definition in the selected file");
      return false;
    }
    const auto *body =
        llvm::dyn_cast_or_null<clang::CompoundStmt>(destructor->getBody());
    if (body == nullptr || (body->body_empty() && !empty_body_allowed)) {
      fail(destructor->getLocation(),
           "the terminal-cleanup slice requires a nonempty destructor body");
      return false;
    }
    return true;
  }

  std::optional<Json> lower_record(const clang::CXXRecordDecl *record) {
    const clang::ASTRecordLayout &layout = context_.getASTRecordLayout(record);
    const std::uint64_t size = layout.getSize().getQuantity();
    const std::uint64_t alignment = layout.getAlignment().getQuantity();
    if (size > std::numeric_limits<std::uint32_t>::max() ||
        alignment > std::numeric_limits<std::uint32_t>::max()) {
      fail(record->getLocation(), "supported C++ record layout is too large");
      return std::nullopt;
    }
    llvm::json::Array fields;
    unsigned index = 0;
    for (const clang::FieldDecl *field : record->fields()) {
      const std::uint64_t bit_offset = layout.getFieldOffset(index++);
      if (stateless_field(field))
        continue;
      const std::uint64_t field_size =
          context_.getTypeSizeInChars(field->getType()).getQuantity();
      if (bit_offset % 8 != 0 ||
          bit_offset / 8 > std::numeric_limits<std::uint32_t>::max() ||
          field_size > std::numeric_limits<std::uint32_t>::max()) {
        fail(field->getLocation(), "supported C++ field layout is too large");
        return std::nullopt;
      }
      auto value_type =
          lower_type(field->getType(), field->getLocation(),
                     direct_source_alias(field->getTypeSourceInfo()));
      if (!value_type) {
        return std::nullopt;
      }
      llvm::json::Object lowered;
      lowered["declaration_id"] = declaration_id(field);
      lowered["name"] = field->getNameAsString();
      lowered["value_type"] = std::move(*value_type);
      lowered["offset_bytes"] = static_cast<std::int64_t>(bit_offset / 8);
      lowered["size_bytes"] = static_cast<std::int64_t>(field_size);
      lowered["span"] = declaration_span(field->getSourceRange());
      fields.push_back(std::move(lowered));
    }
    llvm::json::Object result;
    result["declaration_id"] = declaration_id(record);
    result["name"] = record_name(record);
    result["path"] = record_path(record);
    result["size_bytes"] = static_cast<std::int64_t>(size);
    result["alignment_bytes"] = static_cast<std::int64_t>(alignment);
    result["fields"] = std::move(fields);
    // Its leading bytes hold the vtable pointer, which no field names.
    if (record->isPolymorphic())
      result["polymorphic"] = true;
    // Keep the new nominal type argument even when no field mentions it.
    // The offline importer authenticates its actual locked declaration.
    llvm::json::Array byte_arguments;
    if (const auto *instance =
            llvm::dyn_cast<clang::ClassTemplateSpecializationDecl>(record)) {
      const auto arguments = instance->getTemplateArgs().asArray();
      for (unsigned index = 0; index < arguments.size(); ++index) {
        const auto &argument = arguments[index];
        if (argument.getKind() != clang::TemplateArgument::Type ||
            !supported_byte_enum(argument.getAsType()))
          continue;
        auto value_type = lower_type(argument.getAsType(), record->getLocation());
        if (!value_type) return std::nullopt;
        llvm::json::Object entry;
        entry["index"] = static_cast<std::int64_t>(index);
        entry["value_type"] = std::move(*value_type);
        byte_arguments.push_back(std::move(entry));
      }
    }
    result["byte_template_arguments"] = std::move(byte_arguments);
    if (record->getNumBases() == 1) {
      const auto &base = *record->bases_begin();
      auto value_type = lower_type(base.getType(), base.getBeginLoc());
      if (!value_type) return std::nullopt;
      llvm::json::Object subobject;
      subobject["value_type"] = std::move(*value_type);
      subobject["offset_bytes"] = static_cast<std::int64_t>(
          layout.getBaseClassOffset(base.getType()->getAsCXXRecordDecl()).getQuantity());
      subobject["size_bytes"] = static_cast<std::int64_t>(
          context_.getTypeSizeInChars(base.getType()).getQuantity());
      subobject["span"] = declaration_span(base.getSourceRange());
      result["base"] = std::move(subobject);
    }
    const clang::CXXDestructorDecl *destructor = record->getDestructor();
    if (needs_destructor_body(destructor)) {
      const auto *definition = llvm::dyn_cast_or_null<clang::CXXDestructorDecl>(
          destructor->getDefinition());
      if (definition == nullptr) {
        fail(destructor->getLocation(),
             "the supported destructor has no reachable definition");
        return std::nullopt;
      }
      llvm::json::Object reference;
      reference["declaration_id"] = declaration_id(definition);
      reference["name"] = destructor_name(definition);
      reference["span"] = span(definition->getNameInfo().getSourceRange());
      result["destructor"] = std::move(reference);
    } else {
      result["destructor"] = nullptr;
    }
    result["span"] = declaration_span(record->getSourceRange());
    if (!state_.error.empty()) {
      return std::nullopt;
    }
    return Json(std::move(result));
  }

  bool validate_member_object(const clang::MemberExpr *member,
                              const clang::CXXRecordDecl *owner) {
    // `p->field` reads through a record pointer held by a parameter or a
    // local, which roots the place; a pointer read from a field or returned
    // by a call does not.
    if (member->isArrow() &&
        !llvm::isa<clang::CXXThisExpr>(member->getBase()->IgnoreParenImpCasts()) &&
        !record_pointer_variable(member->getBase())) {
      fail(member->getOperatorLoc(),
           "C++ field projections cannot traverse record pointers; arrow access requires the current object "
           "or a record pointer parameter or local");
      return false;
    }
    auto type = member->getBase()->getType();
    if (const auto *pointer = type->getAs<clang::PointerType>())
      type = pointer->getPointeeType();
    const auto *record = type->getAsCXXRecordDecl();
    if (record == nullptr || record->getCanonicalDecl() != owner->getCanonicalDecl()) {
      fail(member->getMemberLoc(), "C++ field projection has a mismatched record owner");
      return false;
    }
    return remember_record(owner);
  }

  // `new R{v...}`, the allocation of one simple record initialized with one
  // value per field in declaration order, as `expression` when it is one.
  // The global replaceable `operator new` allocates it; its failure throws
  // `std::bad_alloc`, which ends the program in a `noexcept` function, the
  // only place one is admitted. `{"record": ..., "fields": [...]}`.
  std::optional<Json> lower_new_object(const clang::CXXNewExpr *created,
                                       const clang::FunctionDecl *function) {
    const auto *prototype = function->getType()->getAs<clang::FunctionProtoType>();
    const auto *record = record_pointer_target(created->getType());
    const auto *allocator = created->getOperatorNew();
    if (prototype == nullptr || !prototype->isNothrow()) {
      fail(created->getBeginLoc(),
           "a C++ `new` expression is supported in a noexcept function, where a failed "
           "allocation ends the program");
      return std::nullopt;
    }
    if (created->isArray() || created->getNumPlacementArgs() != 0 || record == nullptr ||
        allocator == nullptr || !allocator->isReplaceableGlobalAllocationFunction() ||
        !record->isAggregate() || !record->hasTrivialDestructor() ||
        has_stateless_field(record)) {
      fail(created->getBeginLoc(),
           "a supported C++ `new` allocates one simple aggregate record with the global "
           "operator new");
      return std::nullopt;
    }
    if (!remember_record(record)) return std::nullopt;
    const auto *semantic_list =
        llvm::dyn_cast_or_null<clang::InitListExpr>(created->getInitializer());
    const clang::InitListExpr *syntactic_list = semantic_list;
    if (semantic_list != nullptr && semantic_list->getSyntacticForm() != nullptr)
      syntactic_list = semantic_list->getSyntacticForm();
    const unsigned field_count = std::distance(record->field_begin(), record->field_end());
    if (created->getInitializationStyle() != clang::CXXNewInitializationStyle::Braces ||
        syntactic_list == nullptr || syntactic_list->getNumInits() != field_count) {
      fail(created->getBeginLoc(),
           "a supported C++ `new` requires one direct brace initializer per field in "
           "declaration order");
      return std::nullopt;
    }
    llvm::json::Array fields;
    unsigned index = 0;
    for (const clang::FieldDecl *field : record->fields()) {
      const clang::Expr *field_source = syntactic_list->getInit(index);
      auto value = lower_expression(semantic_list->getInit(index), function);
      ++index;
      if (!value) return std::nullopt;
      llvm::json::Object field_reference;
      field_reference["record_declaration_id"] = declaration_id(record);
      field_reference["declaration_id"] = declaration_id(field);
      field_reference["name"] = field->getNameAsString();
      field_reference["span"] = span(field->getSourceRange());
      llvm::json::Object field_initializer;
      field_initializer["field"] = std::move(field_reference);
      field_initializer["value"] = std::move(*value);
      field_initializer["span"] = span(field_source->getSourceRange());
      fields.push_back(std::move(field_initializer));
    }
    auto record_type = lower_type(created->getAllocatedType(), created->getBeginLoc());
    if (!record_type) return std::nullopt;
    llvm::json::Object result;
    result["record"] = std::move(*record_type);
    result["fields"] = std::move(fields);
    return Json(std::move(result));
  }

  // A default member initializer the importer can read without running
  // code: `nullptr`, or an integer or `bool` literal, as `Node* head =
  // nullptr;` and `unsigned long count = 0;` are.
  static bool constant_member_initializer(const clang::FieldDecl *field) {
    const clang::Expr *value = field->getInClassInitializer();
    if (value == nullptr) return false;
    value = value->IgnoreParenImpCasts();
    return llvm::isa<clang::CXXNullPtrLiteralExpr>(value) ||
           llvm::isa<clang::IntegerLiteral>(value) ||
           llvm::isa<clang::CXXBoolLiteralExpr>(value);
  }

  // A local built by its record's implicit or first-declaration-defaulted
  // default constructor, which only runs each field's default member
  // initializer: every field has a constant one, and the record has no base
  // and trivial destruction. `Stack<int> stack;`
  bool member_initialized_default_construction(const clang::Expr *initializer,
                                               const clang::CXXRecordDecl *record) const {
    const auto *construction =
        llvm::dyn_cast<clang::CXXConstructExpr>(initializer->IgnoreParenImpCasts());
    const auto *constructor =
        construction == nullptr ? nullptr : construction->getConstructor();
    if (constructor == nullptr || !constructor->isDefaultConstructor() ||
        construction->getNumArgs() != 0 || record->getNumBases() != 0 ||
        record->isPolymorphic() || !record->hasTrivialDestructor() ||
        !(constructor->isImplicit() || constructor->isExplicitlyDefaulted()) ||
        has_stateless_field(record) || record->field_empty())
      return false;
    for (const clang::FieldDecl *field : record->fields())
      if (!constant_member_initializer(field)) return false;
    return true;
  }

  // Whether `base`, the object operand of an arrow, reads a parameter or
  // local that holds a record pointer.
  bool record_pointer_variable(const clang::Expr *base) const {
    const auto *cast = llvm::dyn_cast<clang::ImplicitCastExpr>(base->IgnoreParens());
    if (cast == nullptr || cast->getCastKind() != clang::CK_LValueToRValue)
      return false;
    const auto *reference =
        llvm::dyn_cast<clang::DeclRefExpr>(cast->getSubExpr()->IgnoreParens());
    const auto *variable =
        reference == nullptr ? nullptr : llvm::dyn_cast<clang::VarDecl>(reference->getDecl());
    return variable != nullptr && variable->hasLocalStorage() &&
           record_pointer_target(variable->getType()) != nullptr;
  }

  Json field_reference(const clang::MemberExpr *member,
                       const clang::FieldDecl *field) {
    llvm::json::Object result;
    result["record_declaration_id"] = declaration_id(field->getParent());
    result["declaration_id"] = declaration_id(field);
    result["name"] = field->getNameAsString();
    result["span"] = span(member->getMemberNameInfo().getSourceRange());
    return Json(std::move(result));
  }

  std::optional<LoweredMember>
  lower_member(const clang::MemberExpr *member,
               const clang::FunctionDecl *function) {
    const auto *field = llvm::dyn_cast<clang::FieldDecl>(member->getMemberDecl());
    const auto *record = field == nullptr ? nullptr :
        llvm::dyn_cast_or_null<clang::CXXRecordDecl>(field->getParent()->getDefinition());
    if (record == nullptr) {
      fail(member->getMemberLoc(), "the supported C++ member access must resolve to a data field");
      return std::nullopt;
    }
    if (!validate_member_object(member, record)) return std::nullopt;
    auto object = lower_place_reference(member->getBase(), function);
    if (!object || !state_.error.empty()) return std::nullopt;
    return LoweredMember{std::move(*object), field_reference(member, field)};
  }

  std::optional<Json>
  lower_place_reference(const clang::Expr *expression,
                        const clang::FunctionDecl *expected_function) {
    // Walk once from leaf to root, then reverse the mixed field/base edges.
    // Never erase an implicit derived-to-base conversion with IgnoreImpCasts.
    std::vector<Json> reverse_path;
    auto push = [&](Json projection) {
      if (reverse_path.size() >= kMaxRecordDeclarations) {
        fail(expression->getExprLoc(), "C++ artifact budget exhausted: record field projections");
        return false;
      }
      reverse_path.push_back(std::move(projection));
      return true;
    };
    while (true) {
      expression = expression->IgnoreParens();
      if (const auto *cast = llvm::dyn_cast<clang::ImplicitCastExpr>(expression)) {
        if (cast->getCastKind() == clang::CK_DerivedToBase ||
            cast->getCastKind() == clang::CK_UncheckedDerivedToBase) {
          auto source_type = cast->getSubExpr()->getType();
          if (const auto *pointer = source_type->getAs<clang::PointerType>())
            source_type = pointer->getPointeeType();
          const auto *owner = source_type->getAsCXXRecordDecl();
          if (owner != nullptr) owner = owner->getDefinition();
          std::vector<Json> edges;
          if (cast->path_empty()) {
            fail(cast->getExprLoc(), "C++ base conversion requires an explicit nominal base path");
            return std::nullopt;
          }
          // A conversion to a `const` base reference, the last edge of the
          // path, lends the object without the right to change it.
          const bool to_const = cast->getType().isConstQualified();
          std::size_t edge_index = 0;
          for (const auto *base : cast->path()) {
            ++edge_index;
            if (owner == nullptr || !remember_record(owner) ||
                owner->getNumBases() != 1 || base->isVirtual() ||
                base->getAccessSpecifier() != clang::AS_public) {
              if (state_.error.empty())
                fail(cast->getExprLoc(), "C++ base conversion requires a declared public non-virtual base");
              return std::nullopt;
            }
            const auto *target = base->getType()->getAsCXXRecordDecl();
            if (target != nullptr) target = target->getDefinition();
            const auto *declared = owner->bases_begin()->getType()->getAsCXXRecordDecl();
            if (target == nullptr || declared == nullptr ||
                target->getCanonicalDecl() != declared->getCanonicalDecl()) {
              fail(cast->getExprLoc(), "C++ base conversion has a mismatched nominal base path");
              return std::nullopt;
            }
            if (edges.size() + reverse_path.size() >= kMaxRecordDeclarations) {
              fail(cast->getExprLoc(), "C++ artifact budget exhausted: record field projections");
              return std::nullopt;
            }
            llvm::json::Object reference;
            reference["record_declaration_id"] = declaration_id(owner);
            reference["base_declaration_id"] = declaration_id(target);
            reference["base_name"] = record_name(target);
            reference["span"] = span(cast->getSourceRange());
            if (to_const && edge_index == cast->path_size())
              reference["is_const"] = true;
            llvm::json::Object projection;
            projection["base"] = std::move(reference);
            edges.push_back(Json(std::move(projection)));
            owner = target;
          }
          for (auto iterator = edges.rbegin(); iterator != edges.rend(); ++iterator)
            if (!push(std::move(*iterator))) return std::nullopt;
        }
        expression = cast->getSubExpr();
        continue;
      }
      if (const auto *member = llvm::dyn_cast<clang::MemberExpr>(expression)) {
        const auto *field = llvm::dyn_cast<clang::FieldDecl>(member->getMemberDecl());
        const auto *owner = field == nullptr ? nullptr :
            llvm::dyn_cast_or_null<clang::CXXRecordDecl>(field->getParent()->getDefinition());
        if (owner == nullptr || !validate_member_object(member, owner)) {
          if (state_.error.empty())
            fail(member->getMemberLoc(), "C++ field projections require declared data fields");
          return std::nullopt;
        }
        if (!push(field_reference(member, field))) return std::nullopt;
        expression = member->getBase();
        continue;
      }
      break;
    }
    auto finish = [&](llvm::json::Object result) -> std::optional<Json> {
      if (!reverse_path.empty()) {
        llvm::json::Array path;
        for (auto iterator = reverse_path.rbegin(); iterator != reverse_path.rend(); ++iterator)
          path.push_back(std::move(*iterator));
        result["projections"] = std::move(path);
      }
      if (!state_.error.empty()) return std::nullopt;
      return Json(std::move(result));
    };
    if (llvm::isa<clang::CXXThisExpr>(expression)) {
      const auto *method = llvm::dyn_cast<clang::CXXMethodDecl>(expected_function);
      if (method == nullptr || method->isStatic()) {
        fail(expression->getExprLoc(),
             "`this` is supported only inside a method, constructor, or "
             "destructor body");
        return std::nullopt;
      }
      llvm::json::Object result;
      result["declaration_id"] = object_self_id(method);
      result["name"] = "self";
      result["span"] = span(method->getNameInfo().getSourceRange());
      return finish(std::move(result));
    }
    const auto *reference = llvm::dyn_cast<clang::DeclRefExpr>(expression);
    const auto *place =
        reference == nullptr
            ? nullptr
            : llvm::dyn_cast<clang::ValueDecl>(reference->getDecl());
    const auto *variable = llvm::dyn_cast_or_null<clang::VarDecl>(place);
    const bool supported_parameter =
        llvm::isa_and_nonnull<clang::ParmVarDecl>(place);
    const bool supported_local =
        variable != nullptr && !supported_parameter &&
        variable->hasLocalStorage() && !variable->isStaticLocal();
    // A lambda's by-copy capture is one of its leading parameters.
    const auto *lambda_call = llvm::dyn_cast_or_null<clang::CXXMethodDecl>(expected_function);
    const bool lambda_capture =
        variable != nullptr && lambda_call != nullptr && lambda_call->getParent()->isLambda() &&
        reference->refersToEnclosingVariableOrCapture() &&
        llvm::any_of(lambda_call->getParent()->captures(), [&](const clang::LambdaCapture &capture) {
          return capture.capturesVariable() && capture.getCapturedVar() == variable &&
                 capture.getCaptureKind() == clang::LCK_ByCopy;
        });
    if (place == nullptr ||
        (place->getDeclContext() != expected_function &&
         place != active_catch_binding_ && !lambda_capture) ||
        (!supported_parameter && !supported_local)) {
      fail(expression->getExprLoc(),
           "the supported C++ slice can access only current function parameters and automatic locals");
      return std::nullopt;
    }
    llvm::json::Object result;
    result["declaration_id"] = declaration_id(place);
    result["name"] = place->getNameAsString();
    result["span"] = span(reference->getSourceRange());
    if (!state_.error.empty()) {
      return std::nullopt;
    }
    return finish(std::move(result));
  }

  std::string declaration_id(const clang::Decl *declaration) {
    llvm::SmallString<128> result;
    if (clang::index::generateUSRForDecl(declaration, result)) {
      fail(declaration->getLocation(),
           "Clang could not produce a stable declaration identity");
      return {};
    }
    return result.str().str();
  }

  std::string object_self_id(const clang::CXXMethodDecl *method) {
    return declaration_id(method) + "@this";
  }

  Json boolean_constant(bool value, clang::SourceRange source,
                        bool compiler_evaluated) {
    llvm::json::Object integer_type;
    integer_type["kind"] = "integer";
    integer_type["bits"] = 32;
    integer_type["signed"] = true;
    integer_type["is_const"] = false;
    integer_type["source_aliases"] = llvm::json::Array();
    llvm::json::Object integer;
    integer["kind"] =
        compiler_evaluated ? "compiler_constant" : "integer_literal";
    integer["value"] = value ? "1" : "0";
    integer["value_type"] = std::move(integer_type);
    integer["span"] = span(source);
    llvm::json::Object boolean_type;
    boolean_type["kind"] = "boolean";
    boolean_type["bits"] =
        static_cast<std::int64_t>(context_.getTypeSize(context_.BoolTy));
    boolean_type["is_const"] = false;
    llvm::json::Object result;
    result["kind"] = "integral_cast";
    result["value"] = std::move(integer);
    result["value_type"] = std::move(boolean_type);
    result["span"] = span(source);
    return Json(std::move(result));
  }

  const char *builtin_template_type_name(clang::QualType type) const {
    // Keep exact builtin identities: LP64 long and long long have equal widths.
    const std::pair<clang::QualType, const char *> supported[] = {
        {context_.BoolTy, "bool"},
        {context_.IntTy, "int"},
        {context_.UnsignedIntTy, "unsigned_int"},
        {context_.LongTy, "long"},
        {context_.UnsignedLongTy, "unsigned_long"},
        {context_.LongLongTy, "long_long"},
        {context_.UnsignedLongLongTy, "unsigned_long_long"}};
    for (const auto &[candidate, token] : supported) {
      if (context_.hasSameType(type, candidate))
        return token;
    }
    return nullptr;
  }

  std::string template_argument_suffix(
      llvm::ArrayRef<clang::TemplateArgument> arguments,
      clang::SourceLocation location, bool allow_tags) {
    if (allow_tags && arguments.size() > 32) {
      fail(location, "C++ class template instances support at most 32 arguments");
      return {};
    }
    std::string suffix;
    for (const auto &argument : arguments) {
      if (argument.getKind() == clang::TemplateArgument::Integral &&
          argument.getIntegralType()->isBooleanType()) {
        suffix +=
            argument.getAsIntegral().isZero() ? "__bool_false" : "__bool_true";
      } else if (argument.getKind() == clang::TemplateArgument::Integral) {
        const auto type = context_.getCanonicalType(argument.getIntegralType());
        const char *name = builtin_template_type_name(type);
        if (name == nullptr) {
          fail(location, "C++ integral template arguments require bool or "
                         "32/64-bit builtin integers");
          return {};
        }
        llvm::SmallString<32> decimal;
        argument.getAsIntegral().toString(decimal, 10);
        std::string value = std::string(decimal);
        if (!value.empty() && value.front() == '-')
          value.replace(0, 1, "neg_");
        suffix += "__value_" + std::string(name) + "_" + value;
      } else if (argument.getKind() == clang::TemplateArgument::Type &&
                 archetype_name(argument.getAsType()) != nullptr &&
                 !argument.getAsType().hasQualifiers()) {
        suffix += "__param_" + *archetype_name(argument.getAsType());
      } else if (argument.getKind() == clang::TemplateArgument::Type) {
        clang::QualType type = context_.getCanonicalType(argument.getAsType());
        // A class template may take a const native element, as in
        // `std::span<const int>`; other qualifiers stay refused.
        std::string qualifier;
        if (allow_tags && type.isLocalConstQualified() &&
            !type.isLocalVolatileQualified() && !type.isLocalRestrictQualified() &&
            supported_pointer_element(type)) {
          qualifier = "const_";
          type = type.getUnqualifiedType();
        }
        if (type.hasQualifiers()) {
          fail(location,
               "qualified C++ template type arguments are unsupported");
          return {};
        }
        const char *name = builtin_template_type_name(type);
        // A byte-sized element, as in `std::span<unsigned char>`, names a
        // class template instance; integral template values stay 32/64-bit.
        if (name == nullptr && allow_tags &&
            context_.hasSameType(type, context_.UnsignedCharTy))
          name = "unsigned_char";
        if (name == nullptr && allow_tags && supported_byte_enum(type)) {
          const auto *enumeration = type->getAs<clang::EnumType>()->getDecl();
          if (declaration_id(enumeration) == "c:@N@std@E@byte" &&
              enumeration->getQualifiedNameAsString() == "std::byte") {
            suffix += "__" + qualifier + "std_byte";
            continue;
          }
        }
        if (name == nullptr && allow_tags) {
          const auto *tag = type->getAsCXXRecordDecl();
          if (tag != nullptr && tag->getDefinition() != nullptr) {
            tag = tag->getDefinition();
            if (!llvm::isa<clang::ClassTemplateSpecializationDecl>(tag) &&
                !tag->getName().empty() && tag->field_empty() &&
                tag->getNumBases() == 0 && tag->isStandardLayout() &&
                tag->isTriviallyCopyable() && tag->hasTrivialDestructor() &&
                (is_in_logical_source(tag->getLocation()) ||
                 dependency_source(tag->getLocation()))) {
              std::string tag_name = tag->getQualifiedNameAsString();
              size_t pos = 0;
              while ((pos = tag_name.find("::", pos)) != std::string::npos) {
                tag_name.replace(pos, 2, "_");
                ++pos;
              }
              suffix += "__tag_" + tag_name;
              continue;
            }
          }
          fail(location, "C++ class template type arguments require supported "
                         "builtin scalars or named empty trivial tags within the import root");
          return {};
        }
        if (name == nullptr) {
          fail(location, "C++ template type arguments require "
                         "bool or 32/64-bit builtin integers");
          return {};
        }
        suffix += "__" + qualifier + std::string(name);
      } else {
        fail(location, "C++ template arguments require Boolean or 32/64-bit integral "
                       "values or supported scalar types");
        return {};
      }
    }
    return suffix;
  }

  std::string template_suffix(const clang::FunctionDecl *function) {
    const auto *arguments = function->getTemplateSpecializationArgs();
    return arguments == nullptr
               ? std::string{}
               : template_argument_suffix(arguments->asArray(),
                                          function->getLocation(), false);
  }

  std::string record_name(const clang::CXXRecordDecl *record) {
    std::string name = record->getNameAsString();
    if (const auto *instance =
            llvm::dyn_cast<clang::ClassTemplateSpecializationDecl>(record)) {
      name += template_argument_suffix(instance->getTemplateArgs().asArray(),
                                       record->getLocation(), true);
    }
    return name;
  }

  std::string function_name(const clang::FunctionDecl *function) {
    std::string name = without_archetypes(function->getQualifiedNameAsString());
    size_t pos = 0;
    while ((pos = name.find("::", pos)) != std::string::npos) {
      name.replace(pos, 2, "_");
      ++pos;
    }
    return name + template_suffix(function);
  }

  std::string method_name(const clang::CXXMethodDecl *method) {
    std::string name = method->getNameAsString();
    if (method->isOverloadedOperator()) {
      switch (method->getOverloadedOperator()) {
      case clang::OO_PlusEqual:
        name = "operator_add_assign";
        break;
      case clang::OO_MinusEqual:
        name = "operator_subtract_assign";
        break;
      case clang::OO_Subscript:
        name = "operator_index";
        break;
      default:
        fail(method->getLocation(), "the supported C++ operator methods are "
                                    "operator+=, operator-= and operator[] only");
        return {};
      }
    }
    return record_name(method->getParent()) + "_" + name +
           template_suffix(method);
  }

  std::string constructor_name(
      const clang::CXXConstructorDecl *constructor) {
    return record_name(constructor->getParent()) + "_constructor";
  }

  std::string destructor_name(
      const clang::CXXDestructorDecl *destructor) {
    return record_name(destructor->getParent()) + "_destructor";
  }

  std::optional<std::string> executable_source(clang::SourceLocation location) const {
    if (is_in_logical_source(location))
      return logical_source_;
    return dependency_source(location);
  }

  Json span(clang::SourceRange range) {
    if (system_spans_) {
      llvm::json::Object result;
      result["file"] = "<system>";
      result["start_line"] = 0;
      result["start_column"] = 0;
      result["end_line"] = 0;
      result["end_column"] = 0;
      return Json(std::move(result));
    }
    return source_span(range, function_source_.empty() ? logical_source_ : function_source_);
  }

  // At an optimizing level Clang trusts these attributes as promises from the
  // programmer, and Click does not check them. A system-header function is an
  // axiom whose contract Click supplies, so only the project's own
  // declarations are refused (`docs/reference/cli/import.md#optimizer-promises`).
  bool refuse_optimizer_promises(const clang::FunctionDecl *declaration) {
    if (!context_.getLangOpts().Optimize)
      return true;
    auto refuse = [&](const clang::Attr *attribute) {
      if (attribute->isImplicit())
        return false;
      if (!llvm::isa<clang::NonNullAttr, clang::ReturnsNonNullAttr, clang::ConstAttr,
                     clang::PureAttr, clang::LeafAttr, clang::NoReturnAttr,
                     clang::CXX11NoReturnAttr, clang::C11NoReturnAttr,
                     clang::ReturnsTwiceAttr, clang::RestrictAttr, clang::AllocSizeAttr,
                     clang::AllocAlignAttr, clang::AssumeAlignedAttr>(attribute))
        return false;
      fail(attribute->getLocation(),
           std::string("the `") + attribute->getSpelling() +
               "` attribute is an optimizer promise Click does not check; at an "
               "optimizing level Clang trusts it");
      return true;
    };
    for (const clang::FunctionDecl *redeclaration : declaration->redecls()) {
      for (const clang::Attr *attribute : redeclaration->attrs())
        if (refuse(attribute))
          return false;
      for (const clang::ParmVarDecl *parameter : redeclaration->parameters())
        for (const clang::Attr *attribute : parameter->attrs())
          if (refuse(attribute))
            return false;
    }
    return true;
  }

  // A function declared in a system header is an axiom: its interface is
  // exported, its body never is, and Click supplies its contract. The C++
  // standard library is an axiomatic boundary.
  bool is_axiom(const clang::FunctionDecl *function) const {
    return source_manager_.isInSystemHeader(
               source_manager_.getExpansionLoc(function->getLocation()));
  }

  // The interface of a system-header function: its kind, receiver,
  // parameters and return type, but no body. The standard name and
  // canonical signature key the contract Click supplies for it.
  std::optional<Json> lower_axiom(const clang::FunctionDecl *declaration) {
    llvm::SaveAndRestore<bool> spans(system_spans_, true);
    const auto *constructor =
        llvm::dyn_cast<clang::CXXConstructorDecl>(declaration);
    const auto *destructor =
        llvm::dyn_cast<clang::CXXDestructorDecl>(declaration);
    const auto *method = llvm::dyn_cast<clang::CXXMethodDecl>(declaration);
    const bool ordinary_method =
        method != nullptr && constructor == nullptr && destructor == nullptr;
    const auto *prototype =
        declaration->getType()->getAs<clang::FunctionProtoType>();
    if (declaration->isDependentContext() || prototype == nullptr ||
        declaration->isVariadic() ||
        (method != nullptr && (method->isVirtual() || method->isVolatile() ||
                               method->getRefQualifier() != clang::RQ_None))) {
      fail(declaration->getLocation(),
           "standard-library function `" +
               declaration->getQualifiedNameAsString() +
               "` has an interface outside the supported axiomatic slice");
      return std::nullopt;
    }
    if (!prototype->isNothrow()) {
      fail(declaration->getLocation(),
           "standard-library function `" +
               declaration->getQualifiedNameAsString() +
               "` must be noexcept; throwing contracts are not modeled");
      return std::nullopt;
    }
    std::optional<Json> return_type;
    llvm::json::Object function_kind;
    const clang::CXXRecordDecl *record =
        method == nullptr ? nullptr : method->getParent()->getDefinition();
    if (method != nullptr && (record == nullptr || !remember_record(record)))
      return std::nullopt;
    if (constructor != nullptr || destructor != nullptr) {
      llvm::json::Object void_type;
      void_type["kind"] = "void";
      return_type.emplace(std::move(void_type));
      function_kind["kind"] =
          constructor != nullptr ? "constructor" : "destructor";
      function_kind["record_declaration_id"] = declaration_id(record);
      function_kind["record_name"] = record_name(record);
    } else {
      return_type = lower_type(declaration->getReturnType(),
                               declaration->getLocation());
      if (!return_type)
        return std::nullopt;
      function_kind["kind"] =
          ordinary_method ? (method->isStatic() ? "static_method" : "method")
                          : "free";
      if (ordinary_method) {
        function_kind["record_declaration_id"] = declaration_id(record);
        function_kind["record_name"] = record_name(record);
        if (!method->isStatic())
          function_kind["is_const"] = method->isConst();
      }
    }
    llvm::json::Array parameters;
    if (method != nullptr && !method->isStatic()) {
      llvm::json::Object record_type;
      record_type["kind"] = "record";
      record_type["declaration_id"] = declaration_id(record);
      record_type["name"] = record_name(record);
      record_type["is_const"] = method->isConst();
      llvm::json::Object reference_type;
      reference_type["kind"] = "lvalue_reference";
      reference_type["pointee"] = std::move(record_type);
      llvm::json::Object self;
      self["declaration_id"] = object_self_id(method);
      self["name"] = "self";
      self["value_type"] = std::move(reference_type);
      self["span"] = span(method->getNameInfo().getSourceRange());
      parameters.push_back(std::move(self));
    }
    for (const clang::ParmVarDecl *parameter : declaration->parameters()) {
      if (parameter->hasDefaultArg() && constructor != nullptr) {
        fail(parameter->getLocation(),
             "default arguments of standard-library constructors are not modeled");
        return std::nullopt;
      }
      auto lowered = lower_parameter(parameter);
      if (!lowered)
        return std::nullopt;
      parameters.push_back(std::move(*lowered));
    }
    llvm::json::Object axiom;
    axiom["qualified_name"] = declaration->getQualifiedNameAsString();
    axiom["signature"] =
        declaration->getType().getCanonicalType().getAsString();
    llvm::json::Object result;
    result["declaration_id"] = declaration_id(declaration);
    result["name"] = ordinary_method ? method_name(method)
                     : constructor == nullptr
                         ? (destructor == nullptr ? function_name(declaration)
                                                  : destructor_name(destructor))
                         : constructor_name(constructor);
    result["path"] = function_path(declaration);
    result["function_kind"] = std::move(function_kind);
    result["return_type"] = std::move(*return_type);
    result["parameters"] = std::move(parameters);
    result["declared_noexcept"] = true;
    result["span"] = span(declaration->getSourceRange());
    result["body"] = llvm::json::Array();
    result["axiom"] = std::move(axiom);
    if (!state_.error.empty())
      return std::nullopt;
    return Json(std::move(result));
  }

  Json source_span(clang::SourceRange range, const std::string &source) {
    clang::SourceLocation begin =
        source_manager_.getSpellingLoc(range.getBegin());
    clang::SourceLocation end = source_manager_.getSpellingLoc(range.getEnd());
    if (begin.isValid() && end.isValid() &&
        (executable_source(begin) != source || executable_source(end) != source) &&
        (range.getBegin().isMacroID() || range.getEnd().isMacroID())) {
      // Macro bodies can be spelled in another explicitly selected dependency.
      // Keep their definitions in the locked source inventory and label the
      // executable operation at Clang's expansion site in this function.
      const auto begin_source = executable_source(begin);
      const auto end_source = executable_source(end);
      if (begin_source && end_source) {
        if (*begin_source != logical_source_) dependency_sources_.insert(*begin_source);
        if (*end_source != logical_source_) dependency_sources_.insert(*end_source);
        begin = source_manager_.getExpansionLoc(range.getBegin());
        end = source_manager_.getExpansionLoc(range.getEnd());
      }
    }
    if (!begin.isValid() || !end.isValid() || executable_source(begin) != source ||
        executable_source(end) != source) {
      fail(
          begin,
          "C++ executable source locations must stay within their function source");
      return Json(nullptr);
    }
    clang::SourceLocation after = clang::Lexer::getLocForEndOfToken(
        end, 0, source_manager_, context_.getLangOpts());
    const clang::PresumedLoc start = source_manager_.getPresumedLoc(begin);
    const clang::PresumedLoc finish = source_manager_.getPresumedLoc(after);
    if (start.isInvalid() || finish.isInvalid()) {
      fail(begin, "Clang could not resolve a source span");
      return Json(nullptr);
    }
    llvm::json::Object result;
    result["file"] = source;
    result["start_line"] = static_cast<std::int64_t>(start.getLine());
    result["start_column"] = static_cast<std::int64_t>(start.getColumn());
    result["end_line"] = static_cast<std::int64_t>(finish.getLine());
    result["end_column"] = static_cast<std::int64_t>(finish.getColumn());
    return Json(std::move(result));
  }

  Json declaration_span(clang::SourceRange range) {
    const auto source = executable_source(range.getBegin());
    if (!source || executable_source(range.getEnd()) != source) {
      fail(range.getBegin(), "reachable C++ declarations must stay within one declared dependency source");
      return Json(nullptr);
    }
    if (*source != logical_source_)
      dependency_sources_.insert(*source);
    return source_span(range, *source);
  }

  std::optional<std::string>
  dependency_source(clang::SourceLocation location) const {
    const clang::SourceLocation spelling =
        source_manager_.getSpellingLoc(location);
    if (!spelling.isValid()) {
      return std::nullopt;
    }
    const llvm::StringRef filename = source_manager_.getFilename(spelling);
    if (filename.empty()) {
      return std::nullopt;
    }
    std::filesystem::path candidate(filename.str());
    if (candidate.is_relative()) {
      candidate = std::filesystem::path(compilation_directory_) / candidate;
    }
    std::error_code error;
    const std::filesystem::path canonical =
        std::filesystem::canonical(candidate, error);
    if (error) {
      return std::nullopt;
    }
    const std::filesystem::path root = std::filesystem::canonical(
        std::filesystem::path(dependency_root_), error);
    if (error) {
      return std::nullopt;
    }
    const std::filesystem::path relative =
        std::filesystem::relative(canonical, root, error);
    if (error || relative.empty() || relative.is_absolute()) {
      return std::nullopt;
    }
    for (const auto &component : relative) {
      if (component == "..") {
        return std::nullopt;
      }
    }
    return relative.generic_string();
  }

  bool is_in_logical_source(clang::SourceLocation location) const {
    const clang::SourceLocation spelling =
        source_manager_.getSpellingLoc(location);
    if (!spelling.isValid()) {
      return false;
    }
    const llvm::StringRef filename = source_manager_.getFilename(spelling);
    if (filename.empty()) {
      return false;
    }
    std::filesystem::path candidate(filename.str());
    if (candidate.is_relative()) {
      candidate = std::filesystem::path(compilation_directory_) / candidate;
    }
    std::error_code error;
    const std::filesystem::path canonical =
        std::filesystem::weakly_canonical(candidate, error);
    return !error && canonical == std::filesystem::path(logical_source_path_);
  }

  void fail(clang::SourceLocation location, std::string message) {
    if (!state_.error.empty()) {
      return;
    }
    if (location.isValid()) {
      const clang::SourceLocation diagnostic_location =
          source_manager_.getExpansionLoc(location);
      const clang::PresumedLoc presumed =
          source_manager_.getPresumedLoc(diagnostic_location);
      if (presumed.isValid()) {
        const std::string source = is_in_logical_source(diagnostic_location)
                                       ? logical_source_
                                       : dependency_source(diagnostic_location).value_or(
                                             presumed.getFilename());
        state_.error = source + ":" +
                       std::to_string(presumed.getLine()) + ":" +
                       std::to_string(presumed.getColumn()) +
                       ": error: " + std::move(message);
        return;
      }
    }
    state_.error = logical_source_ + ": error: " + std::move(message);
  }

  clang::CompilerInstance &compiler_;
  clang::ASTContext &context_;
  clang::SourceManager &source_manager_;
  std::string logical_source_;
  std::string function_source_;
  std::string logical_source_path_;
  std::vector<std::string> selected_names_;
  std::string dependency_root_;
  std::string compilation_directory_;
  std::string compilation_file_;
  std::vector<std::string> compilation_command_;
  std::string exception_behavior_;
  const std::map<std::string, llvm::json::Value> &library_assertions_;
  std::vector<GenericTemplate> generic_templates_;
  // Every class template of the translation unit, by qualified name.
  std::map<std::string, const clang::ClassTemplateDecl *> class_templates_;
  // Each generic class template, by canonical declaration.
  std::map<const clang::ClassTemplateDecl *, const GenericTemplate *> generic_by_template_;
  // Each abstract type argument's record, by its parameter's name.
  std::map<std::string, const clang::CXXRecordDecl *> archetypes_;
  // Each generic class template's instance at its abstract arguments.
  std::map<const clang::ClassTemplateDecl *, const clang::ClassTemplateSpecializationDecl *>
      archetype_instances_;
  // The template patterns whose bodies were checked to mean the same at
  // every type argument.
  std::set<const clang::FunctionDecl *> checked_generic_patterns_;
  bool system_spans_ = false;
  std::unordered_map<const clang::FunctionDecl *, unsigned> local_declaration_counts_;
  const clang::VarDecl *active_catch_binding_ = nullptr;
  ExportState &state_;
  std::map<std::string, std::vector<clang::FunctionDecl *>> matches_;
  std::unordered_set<const clang::FunctionDecl *> known_functions_;
  std::vector<const clang::FunctionDecl *> reachable_definitions_;
  std::unordered_set<const clang::CXXRecordDecl *> known_records_;
  std::vector<const clang::CXXRecordDecl *> record_definitions_;
  std::set<std::string> dependency_sources_;
  std::unordered_set<const clang::VarDecl *> known_constants_;
  std::vector<const clang::VarDecl *> constant_definitions_;
  std::unordered_set<const clang::FunctionDecl *>
      functions_with_aggregate_local_;
  std::unordered_set<const clang::FunctionDecl *> functions_with_nested_scope_;
  // How many `while` bodies enclose the statement being lowered.
  unsigned loop_depth_ = 0;
  std::unordered_set<const clang::FunctionDecl *>
      functions_with_conditional_scope_;
  std::unordered_map<const clang::FunctionDecl *, unsigned>
      nested_scope_counts_;
  std::unordered_map<const clang::FunctionDecl *,
                     std::vector<const clang::VarDecl *>>
      cleanup_locals_;
};

class ExportConsumer : public clang::ASTConsumer {
public:
  ExportConsumer(clang::CompilerInstance &compiler, const Options &options,
                 ExportState &state)
      : exporter_(compiler, options.logical_source, options.logical_source_path,
                  options.functions, options.dependency_root,
                  options.compilation_directory, options.compilation_file,
                  options.compilation_command, options.exception_behavior,
                  options.library_assertions, options.generic_templates, state) {}

  void HandleTranslationUnit(clang::ASTContext &context) override {
    exporter_.TraverseDecl(context.getTranslationUnitDecl());
    exporter_.finish();
  }

private:
  SemanticExporter exporter_;
};

class PreprocessorFiles : public clang::PPCallbacks {
public:
  PreprocessorFiles(clang::SourceManager &source_manager,
                    std::string compilation_directory, ExportState &state)
      : source_manager_(source_manager),
        compilation_directory_(std::move(compilation_directory)), state_(state) {}

  void LexedFileChanged(clang::FileID file_id,
                        LexedFileChangeReason reason,
                        clang::SrcMgr::CharacteristicKind,
                        clang::FileID, clang::SourceLocation) override {
    if (reason != LexedFileChangeReason::EnterFile || !state_.error.empty()) {
      return;
    }
    auto entry = source_manager_.getFileEntryRefForID(file_id);
    if (!entry) {
      return; // Clang's built-in and command-line buffers are not files.
    }
    std::filesystem::path accessed(entry->getNameAsRequested().str());
    if (accessed.is_relative()) {
      accessed = std::filesystem::path(compilation_directory_) / accessed;
    }
    accessed = accessed.lexically_normal();
    std::error_code error;
    const std::filesystem::path canonical =
        std::filesystem::canonical(accessed, error);
    if (error) {
      state_.error = "error: resolve preprocessor input `" +
                     accessed.generic_string() + "`: " + error.message();
      return;
    }
    const auto [it, inserted] = state_.preprocessor_files.emplace(
        accessed.generic_string(), canonical.generic_string());
    if (!inserted && it->second != canonical.generic_string()) {
      state_.error = "error: preprocessor input `" +
                     accessed.generic_string() + "` changed its target";
    } else if (state_.preprocessor_files.size() > kMaxPreprocessorFiles) {
      state_.error = "error: C++ artifact budget exhausted: preprocessor files (limit " +
                     std::to_string(kMaxPreprocessorFiles) + ")";
    }
  }

private:
  clang::SourceManager &source_manager_;
  std::string compilation_directory_;
  ExportState &state_;
};

class ExportAction : public clang::ASTFrontendAction {
public:
  ExportAction(const Options &options, ExportState &state)
      : options_(options), state_(state) {}

  // Each generic class template's abstract type arguments are declared
  // ahead of the translation unit, in the predefines, which no file holds.
  bool BeginSourceFileAction(clang::CompilerInstance &compiler) override {
    std::set<std::string> names;
    for (const GenericTemplate &generic : options_.generic_templates)
      names.insert(generic.parameters.begin(), generic.parameters.end());
    std::string archetypes;
    for (const std::string &name : names)
      archetypes += "struct " + archetype_record_name(name) +
                    " { unsigned long long __click_word; };\n";
    clang::Preprocessor &preprocessor = compiler.getPreprocessor();
    preprocessor.setPredefines(preprocessor.getPredefines() + archetypes);
    return true;
  }

  std::unique_ptr<clang::ASTConsumer>
  CreateASTConsumer(clang::CompilerInstance &compiler,
                    llvm::StringRef) override {
    compiler.getPreprocessor().addPPCallbacks(
        std::make_unique<PreprocessorFiles>(compiler.getSourceManager(),
                                            options_.compilation_directory,
                                            state_));
    return std::make_unique<ExportConsumer>(compiler, options_,
                                            state_);
  }

private:
  const Options &options_;
  ExportState &state_;
};

class ExportActionFactory : public clang::tooling::FrontendActionFactory {
public:
  ExportActionFactory(const Options &options, ExportState &state)
      : options_(options), state_(state) {}

  std::unique_ptr<clang::FrontendAction> create() override {
    return std::make_unique<ExportAction>(options_, state_);
  }

private:
  const Options &options_;
  ExportState &state_;
};

} // namespace

int main(int argc, const char **argv) {
  // The pinned Clang's resource directory, which Click labels in a lock so
  // the builtin headers read from it are not named by this installation's
  // path.
  if (argc == 2 && std::string(argv[1]) == "--print-resource-dir") {
    llvm::outs() << kClangResourceDir << "\n";
    return 0;
  }
  auto options = parse_options(argc, argv);
  if (!options) {
    return 2;
  }
  const std::string clang_version = clang::getClangFullVersion();
  if (clang_version.find(kClangVersion) == std::string::npos) {
    llvm::errs() << "error: click-cpp-exporter requires Clang " << kClangVersion
                 << "; linked frontend is " << clang_version << "\n";
    return 2;
  }

  std::string database_error;
  auto database = clang::tooling::JSONCompilationDatabase::loadFromFile(
      options->compilation_database, database_error,
      clang::tooling::JSONCommandLineSyntax::AutoDetect);
  if (database == nullptr) {
    llvm::errs() << "error: load C++ compilation database: " << database_error
                 << "\n";
    return 2;
  }
  const auto commands = database->getCompileCommands(options->source);
  if (commands.empty()) {
    llvm::errs() << "error: C++ compilation database has no command for `"
                 << options->source << "`\n";
    return 2;
  }
  if (commands.size() != 1) {
    llvm::errs() << "error: C++ compilation database has " << commands.size()
                 << " commands for `" << options->source
                 << "`; exactly one is required\n";
    return 2;
  }
  const clang::tooling::CompileCommand &command = commands.front();
  if (command.CommandLine.empty()) {
    llvm::errs() << "error: selected C++ compilation command is empty\n";
    return 2;
  }
  const std::string driver =
      std::filesystem::path(command.CommandLine.front()).filename().string();
  if (driver != "clang++" && driver != "clang++-19") {
    llvm::errs() << "error: selected C++ compilation command must use the "
                    "pinned Clang driver, not `"
                 << command.CommandLine.front() << "`\n";
    return 2;
  }
  for (const std::string &argument : command.CommandLine) {
    if (has_untracked_preprocessor_input(argument)) {
      llvm::errs() << "error: selected C++ compilation command has untracked "
                      "preprocessor input mode `"
                   << argument << "`\n";
      return 2;
    }
  }
  options->compilation_directory = command.Directory;
  options->compilation_file = command.Filename;
  options->compilation_command = command.CommandLine;
  clang::tooling::ClangTool tool(*database, {options->source});
  // A command that names no resource directory gets the pinned Clang's, not
  // one derived from where this executable happens to be installed.
  const bool names_resource_dir = std::any_of(
      command.CommandLine.begin(), command.CommandLine.end(),
      [](const std::string &argument) {
        return argument == "-resource-dir" ||
               argument.rfind("-resource-dir=", 0) == 0;
      });
  if (!names_resource_dir) {
    tool.appendArgumentsAdjuster(clang::tooling::getInsertArgumentAdjuster(
        (std::string("-resource-dir=") + kClangResourceDir).c_str(),
        clang::tooling::ArgumentInsertPosition::END));
  }
  ExportState state;
  ExportActionFactory factory(*options, state);
  const int status = tool.run(&factory);
  if (status != 0) {
    return status;
  }
  if (!state.error.empty()) {
    llvm::errs() << state.error << "\n";
    return 1;
  }
  if (!state.artifact) {
    llvm::errs() << "error: C++ exporter produced no semantic artifact\n";
    return 1;
  }
  llvm::outs() << llvm::formatv("{0:2}", *state.artifact) << "\n";
  return 0;
}
