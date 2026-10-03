#include <algorithm>
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
#include "clang/Basic/SourceManager.h"
#include "clang/Basic/Version.h"
#include "clang/Frontend/CompilerInstance.h"
#include "clang/Frontend/FrontendAction.h"
#include "clang/Index/USRGeneration.h"
#include "clang/Lex/Lexer.h"
#include "clang/Lex/PPCallbacks.h"
#include "clang/Lex/Preprocessor.h"
#include "clang/Tooling/CompilationDatabase.h"
#include "clang/Tooling/JSONCompilationDatabase.h"
#include "clang/Tooling/Tooling.h"
#include "llvm/ADT/SmallString.h"
#include "llvm/Support/JSON.h"
#include "llvm/Support/raw_ostream.h"

namespace {
// Resource policy; the independent artifact checker enforces the same bounds.
constexpr std::size_t kMaxRecordDeclarations = 256;
constexpr std::size_t kMaxConstantDeclarations = 1024;
constexpr std::size_t kMaxFunctionDeclarations = 1024;

constexpr const char *kClangVersion = "19.1.7";
constexpr std::size_t kMaxPreprocessorFiles = 4096;

struct Options {
  std::string logical_source;
  std::string logical_source_path;
  std::string function;
  std::string source;
  std::string dependency_root;
  std::string compilation_database;
  std::string exception_behavior = "normal_only";
  std::string compilation_directory;
  std::string compilation_file;
  std::vector<std::string> compilation_command;
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
      result.function = value;
    } else if (option == "--source") {
      result.source = value;
    } else if (option == "--dependency-root") {
      result.dependency_root = value;
    } else if (option == "--compilation-database") {
      result.compilation_database = value;
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
      result.function.empty() || result.source.empty() ||
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
  SemanticExporter(clang::ASTContext &context, std::string logical_source,
                   std::string logical_source_path,
                   std::string selected_name,
                   std::string dependency_root,
                   std::string compilation_directory,
                   std::string compilation_file,
                   std::vector<std::string> compilation_command,
                   std::string exception_behavior,
                   ExportState &state)
      : context_(context), source_manager_(context.getSourceManager()),
        logical_source_(std::move(logical_source)),
        logical_source_path_(std::move(logical_source_path)),
        selected_name_(std::move(selected_name)),
        dependency_root_(std::move(dependency_root)),
        compilation_directory_(std::move(compilation_directory)),
        compilation_file_(std::move(compilation_file)),
        compilation_command_(std::move(compilation_command)),
        exception_behavior_(std::move(exception_behavior)), state_(state) {}

  bool VisitFunctionDecl(clang::FunctionDecl *declaration) {
    if (declaration->isThisDeclarationADefinition() &&
        declaration->getQualifiedNameAsString() == selected_name_ &&
        is_in_logical_source(declaration->getLocation())) {
      matches_.push_back(declaration);
    }
    return true;
  }

  void finish() {
    if (exception_behavior_ == "scalar_int32" &&
        !context_.getLangOpts().CXXExceptions) {
      fail({}, "scalar int32 exception profile requires C++ exceptions enabled");
      return;
    }
    if (matches_.empty()) {
      fail({}, "selected function `" + selected_name_ + "` was not found");
      return;
    }
    if (matches_.size() != 1) {
      fail(matches_.front()->getLocation(),
           "selected function `" + selected_name_ + "` is overloaded");
      return;
    }
    const clang::FunctionDecl *selected = matches_.front()->getDefinition();
    if (selected == nullptr) {
      fail(matches_.front()->getLocation(),
           "selected function has no reachable definition");
      return;
    }
    known_functions_.insert(selected->getCanonicalDecl());
    auto function = lower_function(selected);
    if (!function) {
      return;
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
      auto lowered = lower_constant(constant, selected);
      if (!lowered) {
        return;
      }
      constants.push_back(std::move(*lowered));
    }
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
    artifact["schema"] = 33;
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
    artifact["function"] = std::move(*function);
    artifact["reachable_functions"] = std::move(reachable_functions);
    state_.artifact.emplace(std::move(artifact));
  }

private:
  enum class CleanupScopeKind { None, Conditional, Try };

  using Json = llvm::json::Value;

  struct LoweredCall {
    llvm::json::Object callee;
    llvm::json::Array arguments;
    Json span;
  };

  struct LoweredMember {
    Json object;
    Json field;
  };

  std::optional<Json> lower_function(const clang::FunctionDecl *declaration) {
    if (declaration->isDependentContext() ||
        declaration->getType()->isDependentType()) {
      fail(declaration->getLocation(),
           "select an ordinary C++ caller of concrete template instances, not "
           "a dependent template pattern");
      return std::nullopt;
    }
    const auto *constructor =
        llvm::dyn_cast<clang::CXXConstructorDecl>(declaration);
    const auto *destructor =
        llvm::dyn_cast<clang::CXXDestructorDecl>(declaration);
    const auto *method = llvm::dyn_cast<clang::CXXMethodDecl>(declaration);
    const bool ordinary_method =
        method != nullptr && constructor == nullptr && destructor == nullptr;
    if (ordinary_method && (method->isVirtual() || method->isVolatile() ||
                            method->getRefQualifier() != clang::RQ_None ||
                            method->isDeleted() || method->isVariadic())) {
      fail(method->getLocation(),
           "supported C++ methods must be non-virtual, "
           "non-volatile, non-deleted, unqualified, and non-variadic");
      return std::nullopt;
    }
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
      function_kind["record_name"] = record->getNameAsString();
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
        function_kind["record_name"] = record->getNameAsString();
        if (!method->isStatic())
          function_kind["is_const"] = method->isConst();
      }
    }
    llvm::json::Array parameters;
    if (method != nullptr && !method->isStatic()) {
      const auto *method = llvm::cast<clang::CXXMethodDecl>(declaration);
      const auto *record = method->getParent()->getDefinition();
      llvm::json::Object record_type;
      record_type["kind"] = "record";
      record_type["declaration_id"] = declaration_id(record);
      record_type["name"] = record->getNameAsString();
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
    if (body == nullptr || (body->body_empty() && constructor == nullptr)) {
      fail(declaration->getLocation(),
           "the supported C++ function requires a nonempty compound body");
      return std::nullopt;
    }

    llvm::json::Array statements;
    if (constructor != nullptr) {
      const auto *record = constructor->getParent()->getDefinition();
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
        auto value = lower_expression(initializer->getInit(), constructor);
        if (!value) {
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
        statement["kind"] = "member_store";
        statement["object"] = std::move(object);
        statement["field"] = std::move(field_reference);
        statement["value"] = std::move(*value);
        statement["span"] = span(initializer->getSourceRange());
        statements.push_back(std::move(statement));
      }
    }
    for (const clang::Stmt *statement : body->body()) {
      auto lowered = lower_statement(statement, declaration, true, true);
      if (!lowered) {
        return std::nullopt;
      }
      statements.push_back(std::move(*lowered));
    }

    llvm::json::Object result;
    result["declaration_id"] = declaration_id(declaration);
    result["name"] = ordinary_method ? method_name(method)
                     : constructor == nullptr
                         ? (destructor == nullptr ? function_name(declaration)
                                                  : destructor_name(destructor))
                         : constructor_name(constructor);
    result["function_kind"] = std::move(function_kind);
    result["return_type"] = std::move(*return_type);
    result["parameters"] = std::move(parameters);
    result["declared_noexcept"] = prototype->isNothrow();
    result["span"] = span(declaration->getSourceRange());
    result["body"] = std::move(statements);
    if (!state_.error.empty()) {
      return std::nullopt;
    }
    return Json(std::move(result));
  }

  std::optional<Json> lower_parameter(const clang::ParmVarDecl *parameter) {
    const auto *reference =
        parameter->getType()->getAs<clang::LValueReferenceType>();
    const bool int_reference =
        reference != nullptr &&
        !reference->getPointeeType().isVolatileQualified() &&
        !reference->getPointeeType().isRestrictQualified() &&
        (context_.hasSameType(reference->getPointeeType().getUnqualifiedType(),
                              context_.IntTy) ||
         (reference->getPointeeType()->isSignedIntegerType() &&
          reference->getPointeeType().isConstQualified() &&
          context_.getTypeSize(reference->getPointeeType()) == 64));
    const clang::CXXRecordDecl *record_reference = nullptr;
    if (reference != nullptr &&
        !reference->getPointeeType().isVolatileQualified() &&
        !reference->getPointeeType().isRestrictQualified()) {
      if (const auto *record_type =
              reference->getPointeeType()->getAs<clang::RecordType>()) {
        record_reference = llvm::dyn_cast<clang::CXXRecordDecl>(
            record_type->getDecl()->getDefinition());
      }
    }
    const auto *pointer = parameter->getType()->getAs<clang::PointerType>();
    const bool mutable_int_pointer =
        pointer != nullptr && !parameter->getType().hasQualifiers() &&
        !pointer->getPointeeType().hasQualifiers() &&
        context_.hasSameType(pointer->getPointeeType().getUnqualifiedType(),
                             context_.IntTy);
    const bool by_value_integer =
        !parameter->getType().hasQualifiers() &&
        parameter->getType()->isIntegerType() &&
        (context_.getTypeSize(parameter->getType()) == 32 ||
         context_.getTypeSize(parameter->getType()) == 64);
    const bool by_value_bool =
        reference == nullptr &&
        context_.hasSameType(parameter->getType().getUnqualifiedType(),
                             context_.BoolTy) &&
        !parameter->getType().isConstQualified();
    if (!int_reference && record_reference == nullptr && !mutable_int_pointer &&
        !by_value_bool && !by_value_integer) {
      fail(parameter->getLocation(),
           "the supported C++ parameter must be a by-value bool or "
           "signed/unsigned "
           "32/64-bit integer, int&, const "
           "int&, const signed-64 reference, or mutable int* parameter, or a "
           "mutable or const simple-record reference parameter");
      return std::nullopt;
    }
    if (record_reference != nullptr && !remember_record(record_reference)) {
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

  std::optional<Json>
  lower_type(clang::QualType type, clang::SourceLocation location,
             const clang::TypedefNameDecl *source_alias = nullptr) {
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
    if (const auto *record_type = type->getAs<clang::RecordType>()) {
      const auto *record = llvm::dyn_cast<clang::CXXRecordDecl>(
          record_type->getDecl()->getDefinition());
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
      result["name"] = record->getNameAsString();
      result["is_const"] = type.isConstQualified();
      return Json(std::move(result));
    }
    if (context_.hasSameType(type.getUnqualifiedType(), context_.BoolTy)) {
      llvm::json::Object result;
      result["kind"] = "boolean";
      result["bits"] = static_cast<std::int64_t>(context_.getTypeSize(type));
      result["is_const"] = type.isConstQualified();
      return Json(std::move(result));
    }
    if (!type->isIntegerType() || (context_.getTypeSize(type) != 32 &&
                                   context_.getTypeSize(type) != 64)) {
      fail(location, "the supported C++ slice supports bool, signed/unsigned "
                     "32/64-bit integers, selected signed references, mutable "
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
      source_alias["span"] = alias_span(alias_declaration->getSourceRange());
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

  std::optional<Json> lower_statement(const clang::Stmt *statement,
                                      const clang::FunctionDecl *function,
                                      bool allow_local_declaration,
                                      bool allow_nested_scope) {
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
      return lower_call(call, function);
    }
    if (const auto *binary = llvm::dyn_cast<clang::BinaryOperator>(statement)) {
      if (binary->getOpcode() != clang::BO_Assign &&
          binary->getOpcode() != clang::BO_AddAssign &&
          binary->getOpcode() != clang::BO_SubAssign) {
        fail(binary->getOperatorLoc(),
             "the first C++ slice supports only simple assignment statements");
        return std::nullopt;
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
            !left->getType()->isSignedIntegerType()) {
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
      if (const auto *member = llvm::dyn_cast<clang::MemberExpr>(left)) {
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
      const auto *call = llvm::dyn_cast<clang::CallExpr>(
          returned->getRetValue()->IgnoreParens());
      if (call != nullptr && !is_numeric_limits_max_call(call)) {
        const auto *callee = call->getDirectCallee();
        if (callee == nullptr ||
            !context_.hasSameType(callee->getReturnType(),
                                  function->getReturnType())) {
          fail(call->getExprLoc(), "C++ return call requires matching callee "
                                   "and caller return types");
          return std::nullopt;
        }
        auto lowered = lower_call_operation(call, function, true);
        auto value_type = lower_type(call->getType(), call->getExprLoc());
        if (!lowered || !value_type) {
          return std::nullopt;
        }
        result["kind"] = "return_call";
        result["callee"] = std::move(lowered->callee);
        result["arguments"] = std::move(lowered->arguments);
        result["value_type"] = std::move(*value_type);
      } else {
        auto value = lower_expression(returned->getRetValue(), function);
        if (!value) {
          return std::nullopt;
        }
        result["kind"] = "return";
        result["value"] = std::move(*value);
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
      auto condition = lower_expression(conditional->getCond(), function);
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
        if (destructor != nullptr && !destructor->isImplicit()) {
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
    const bool mutable_int = local->getType()->isIntegerType() &&
                             (context_.getTypeSize(local->getType()) == 32 ||
                              context_.getTypeSize(local->getType()) == 64) &&
                             !local->getType().hasQualifiers();
    const auto *record_type = local->getType()->getAs<clang::RecordType>();
    const auto *record =
        record_type == nullptr
            ? nullptr
            : llvm::dyn_cast<clang::CXXRecordDecl>(
                  record_type->getDecl()->getDefinition());
    const bool record_object =
        record != nullptr && !local->getType().hasQualifiers();
    if (record_object && context_.getLangOpts().CXXExceptions &&
        exception_behavior_ == "normal_only") {
      fail(local->getLocation(),
           "exception-enabled normal-only C++ supports borrowed records only, "
           "not local object construction");
      return std::nullopt;
    }
    if (!mutable_int && !record_object) {
      fail(local->getLocation(),
           "the supported automatic C++ local must resolve to mutable "
           "signed/unsigned "
           "32/64-bit integer or one simple record object");
      return std::nullopt;
    }
    if (!local->hasInit()) {
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
      const bool destructible = destructor != nullptr && !destructor->isImplicit();
      if (function_body_local) {
        if (functions_with_nested_scope_.contains(canonical)) {
          fail(local->getLocation(),
               "nested-scope cleanup cannot yet be combined with an outer aggregate object");
          return std::nullopt;
        }
        if (!functions_with_aggregate_local_.insert(canonical).second) {
          const auto previous = cleanup_locals_.find(canonical);
          if (!destructible || previous == cleanup_locals_.end() ||
              previous->second.size() != 1) {
            fail(local->getLocation(),
                 "the supported C++ slice permits one aggregate object or exactly two destructible objects per function");
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

    llvm::json::Object initializer;
    const clang::Expr *source_initializer = local->getInit();
    const clang::Expr *semantic_initializer =
        source_initializer->IgnoreParenImpCasts();
    if (record_object && record->isAggregate()) {
      const auto *semantic_list =
          llvm::dyn_cast<clang::InitListExpr>(source_initializer);
      const clang::InitListExpr *syntactic_list = semantic_list;
      if (semantic_list != nullptr && semantic_list->getSyntacticForm() != nullptr) {
        syntactic_list = semantic_list->getSyntacticForm();
      }
      const unsigned field_count = std::distance(record->field_begin(),
                                                 record->field_end());
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
    } else if (const auto *call =
            llvm::dyn_cast<clang::CallExpr>(semantic_initializer)) {
      if (call->getDirectCallee() == nullptr ||
          !context_.hasSameType(call->getDirectCallee()->getReturnType(),
                                local->getType())) {
        fail(call->getExprLoc(),
             "C++ call capture requires matching return and local types");
        return std::nullopt;
      }
      auto lowered = lower_call_operation(call, function, true);
      if (!lowered) {
        return std::nullopt;
      }
      initializer["kind"] = "call";
      initializer["callee"] = std::move(lowered->callee);
      initializer["arguments"] = std::move(lowered->arguments);
      initializer["span"] = std::move(lowered->span);
    } else {
      auto value = lower_expression(source_initializer, function);
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
    if (!has_outer_aggregate && scope_count == 2) {
      fail(scope->getLBracLoc(),
           "the supported C++ slice permits at most two sibling cleanup scopes per function");
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
    if (local_count != new_count || new_count == 0 || new_count > 2) {
      fail(scope->getLBracLoc(),
           "the nested-scope slice requires one or two destructible objects and no other locals");
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

  std::optional<LoweredCall>
  lower_call_operation(const clang::CallExpr *call,
                       const clang::FunctionDecl *caller,
                       bool allow_nested = false) {
    const clang::FunctionDecl *callee = call->getDirectCallee();
    if (callee == nullptr) {
      fail(call->getExprLoc(),
           "the supported C++ slice requires a direct free-function call");
      return std::nullopt;
    }
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
    if (has_receiver) {
      if (method->isVirtual() || llvm::isa<clang::CXXConstructorDecl>(method) ||
          llvm::isa<clang::CXXDestructorDecl>(method)) {
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
    if (definition == nullptr) {
      fail(call->getExprLoc(),
           "direct C++ call has no reachable function definition");
      return std::nullopt;
    }
    const clang::SourceLocation definition_location =
        source_manager_.getSpellingLoc(definition->getLocation());
    if (!is_in_logical_source(definition_location)) {
      fail(call->getExprLoc(),
           "the supported C++ call graph requires definitions in the selected file");
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
        if (nested != nullptr && !is_numeric_limits_max_call(nested))
          ++nested_calls;
      }
      if (nested_calls > 1 || (nested_calls != 0 && has_receiver)) {
        fail(call->getExprLoc(),
             "nested C++ call arguments require one call and stable scalar "
             "siblings to preserve evaluation order");
        return std::nullopt;
      }
      if (nested_calls == 1) {
        for (unsigned index = argument_offset; index < call->getNumArgs();
             ++index) {
          const auto *argument = call->getArg(index);
          const auto *nested =
              llvm::dyn_cast<clang::CallExpr>(argument->IgnoreParens());
          if (nested != nullptr && !is_numeric_limits_max_call(nested))
            continue;
          if (!stable_scalar_argument(argument, caller)) {
            fail(argument->getExprLoc(),
                 "nested C++ call arguments require one call and stable scalar "
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

    Json call_span = span(call->getSourceRange());
    if (!state_.error.empty()) {
      return std::nullopt;
    }
    return LoweredCall{std::move(reference), std::move(arguments),
                       std::move(call_span)};
  }

  std::optional<Json>
  lower_call_argument(const clang::Expr *argument,
                      const clang::ParmVarDecl *parameter,
                      const clang::FunctionDecl *caller) {
    llvm::json::Object result;
    if (parameter->getType()->getAs<clang::LValueReferenceType>() != nullptr) {
      auto place = lower_place_reference(argument, caller);
      if (!place) {
        return std::nullopt;
      }
      result["kind"] = "reference";
      result["place"] = std::move(*place);
      return Json(std::move(result));
    }
    if (parameter->getType()->getAs<clang::PointerType>() != nullptr) {
      auto value = lower_expression(argument, caller);
      if (!value) {
        return std::nullopt;
      }
      result["kind"] = "value";
      result["value"] = std::move(*value);
      return Json(std::move(result));
    }
    if (!parameter->getType().hasQualifiers() &&
        (context_.hasSameType(parameter->getType(), context_.BoolTy) ||
         (parameter->getType()->isIntegerType() &&
          (context_.getTypeSize(parameter->getType()) == 32 ||
           context_.getTypeSize(parameter->getType()) == 64)))) {
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
    if (statement == nullptr) {
      return result;
    }
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
            destructor != nullptr && !destructor->isImplicit();
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
    if (!is_in_logical_source(definition->getLocation())) {
      fail(definition->getLocation(),
           "reachable C++ constants must be declared in the selected source");
      return false;
    }
    const bool internal_namespace_constant =
        definition->getDeclContext()->isFileContext() &&
        definition->getFormalLinkage() == clang::Linkage::Internal;
    if (!definition->isConstexpr() ||
        (definition->getStorageClass() != clang::SC_Static &&
         !internal_namespace_constant) ||
        !definition->hasGlobalStorage()) {
      fail(definition->getLocation(),
           "reachable C++ constants must be namespace-scope static constexpr "
           "or internal-linkage constexpr declarations");
      return false;
    }
    const clang::QualType type = definition->getType();
    if (!type.isConstQualified() || !type->isSignedIntegerType() ||
        context_.getTypeSize(type) != 64) {
      fail(definition->getLocation(),
           "reachable C++ constants must have const signed 64-bit type");
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
    const clang::Expr *initializer = constant->getInit();
    const clang::Expr *semantic =
        initializer == nullptr ? nullptr : initializer->IgnoreParenImpCasts();
    const auto *binary = llvm::dyn_cast_or_null<clang::BinaryOperator>(semantic);
    if (semantic == nullptr ||
        (!llvm::isa<clang::IntegerLiteral>(semantic) &&
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
    auto value_type = lower_type(cast->getType(), cast->getExprLoc());
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

  std::optional<Json> lower_expression(const clang::Expr *expression,
                                       const clang::FunctionDecl *function) {
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
    if (const auto *boolean =
            llvm::dyn_cast<clang::CXXBoolLiteralExpr>(expression)) {
      return boolean_constant(boolean->getValue(), boolean->getSourceRange(),
                              false);
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
          (context_.getTypeSize(expression->getType()) == 32 ||
           context_.getTypeSize(expression->getType()) == 64) &&
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
    if (const auto *cast =
            llvm::dyn_cast<clang::ExplicitCastExpr>(expression)) {
      if (cast->getCastKind() == clang::CK_NoOp &&
          context_.hasSameType(cast->getType(),
                               cast->getSubExpr()->getType()) &&
          (cast->getType()->isBooleanType() ||
           (cast->getType()->isIntegerType() &&
            (context_.getTypeSize(cast->getType()) == 32 ||
             context_.getTypeSize(cast->getType()) == 64)))) {
        return lower_expression(cast->getSubExpr(), function);
      }
      if (cast->getCastKind() != clang::CK_IntegralCast &&
          cast->getCastKind() != clang::CK_IntegralToBoolean &&
          cast->getCastKind() != clang::CK_BooleanToSignedIntegral) {
        fail(cast->getExprLoc(), "unsupported explicit C++ conversion");
        return std::nullopt;
      }
      auto value = lower_expression(cast->getSubExpr(), function);
      auto value_type = lower_type(cast->getType(), cast->getExprLoc());
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
        unary != nullptr && unary->getOpcode() == clang::UO_Minus) {
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
        auto value_type = lower_type(cast->getType(), cast->getExprLoc());
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
      auto value_type = lower_type(cast->getType(), cast->getExprLoc());
      if (!value_type) {
        return std::nullopt;
      }
      llvm::json::Object result;
      const clang::Expr *source = cast->getSubExpr()->IgnoreParens();
      if (const auto *reference = llvm::dyn_cast<clang::DeclRefExpr>(source);
          reference != nullptr &&
          llvm::isa<clang::VarDecl>(reference->getDecl()) &&
          !llvm::isa<clang::ParmVarDecl>(reference->getDecl()) &&
          llvm::cast<clang::VarDecl>(reference->getDecl())->hasGlobalStorage()) {
        return lower_constant_reference(reference, cast);
      }
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
      result["span"] = span(cast->getSourceRange());
      return Json(std::move(result));
    }
    if (const auto *address = llvm::dyn_cast<clang::UnaryOperator>(expression);
        address != nullptr && address->getOpcode() == clang::UO_AddrOf) {
      const clang::Expr *operand = address->getSubExpr()->IgnoreParenImpCasts();
      const auto *reference = llvm::dyn_cast<clang::DeclRefExpr>(operand);
      const auto *parameter =
          reference == nullptr
              ? nullptr
              : llvm::dyn_cast<clang::ParmVarDecl>(reference->getDecl());
      const auto *reference_type =
          parameter == nullptr
              ? nullptr
              : parameter->getType()->getAs<clang::LValueReferenceType>();
      if (parameter == nullptr || parameter->getDeclContext() != function ||
          reference_type == nullptr ||
          reference_type->getPointeeType().isConstQualified() ||
          !context_.hasSameType(
              reference_type->getPointeeType().getUnqualifiedType(),
              context_.IntTy)) {
        fail(address->getOperatorLoc(),
             "supported C++ address-of must name a mutable int& parameter");
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
      if (binary->getOpcode() == clang::BO_Add ||
          binary->getOpcode() == clang::BO_Sub ||
          binary->getOpcode() == clang::BO_Mul ||
          binary->getOpcode() == clang::BO_Div ||
          binary->getOpcode() == clang::BO_Rem) {
        if (!binary->getType()->isIntegerType() ||
            (context_.getTypeSize(binary->getType()) != 32 &&
             context_.getTypeSize(binary->getType()) != 64)) {
          fail(binary->getOperatorLoc(),
               "C++ arithmetic requires signed/unsigned 32/64-bit operands; "
               "pointer "
               "arithmetic is unsupported");
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
      if (record_definitions_.size() >= kMaxRecordDeclarations) {
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

  bool validate_record(const clang::CXXRecordDecl *record) {
    if (llvm::isa<clang::ClassTemplateSpecializationDecl>(record)) {
      fail(record->getLocation(),
           "C++ class template instances are unsupported");
      return false;
    }
    if (!record->isStruct() || record->getName().empty()) {
      fail(record->getLocation(),
           "the supported C++ record must be a named struct");
      return false;
    }
    if (!is_in_logical_source(record->getLocation())) {
      fail(record->getLocation(),
           "the supported C++ record must be declared in the selected file");
      return false;
    }
    if (!record->isStandardLayout() || record->getNumBases() != 0) {
      fail(record->getLocation(),
           "the supported C++ record must be standard-layout and trivially-copyable except for a supported destructor, and have no bases");
      return false;
    }
    if (record->field_empty()) {
      fail(record->getLocation(),
           "the supported C++ record must contain at least one field");
      return false;
    }
    const clang::CXXDestructorDecl *supported_destructor =
        record->getDestructor();
    if (supported_destructor != nullptr &&
        !supported_destructor->isImplicit()) {
      if (!validate_destructor(supported_destructor, record))
        return false;
    } else if (!record->isTriviallyCopyable() ||
               !record->hasTrivialDestructor()) {
      fail(record->getLocation(),
           "a record without a supported destructor must remain trivially copyable with trivial destruction");
      return false;
    }
    for (const clang::FieldDecl *field : record->fields()) {
      const clang::QualType type = field->getType();
      const auto *pointer = type->getAs<clang::PointerType>();
      const bool mutable_int =
          !type.hasQualifiers() &&
          (context_.hasSameType(type.getUnqualifiedType(), context_.IntTy) ||
           (type->isSignedIntegerType() && context_.getTypeSize(type) == 64));
      const bool mutable_int_pointer =
          pointer != nullptr && !type.hasQualifiers() &&
          !pointer->getPointeeType().hasQualifiers() &&
          context_.hasSameType(pointer->getPointeeType().getUnqualifiedType(),
                               context_.IntTy);
      if (field->getAccess() != clang::AS_public || field->isBitField() ||
          field->isMutable() || field->hasInClassInitializer() ||
          field->getName().empty() ||
          (!mutable_int && !mutable_int_pointer)) {
        fail(
            field->getLocation(),
            "the supported C++ record fields must be named public mutable int, "
            "signed 64-bit integer, or mutable int* fields without bit-fields");
        return false;
      }
    }
    return true;
  }

  bool validate_constructor(const clang::CXXConstructorDecl *constructor,
                            const clang::CXXRecordDecl *record) {
    const auto *prototype =
        constructor->getType()->getAs<clang::FunctionProtoType>();
    if (!constructor->isExplicit() || constructor->getAccess() != clang::AS_public ||
        constructor->isDefaultConstructor() ||
        constructor->isCopyOrMoveConstructor() ||
        constructor->isDelegatingConstructor() || constructor->isVariadic() ||
        prototype == nullptr || !prototype->isNothrow()) {
      fail(constructor->getLocation(),
           "the supported constructor must be one public explicit non-default noexcept constructor without copying, moving, delegation, or variadic arguments");
      return false;
    }
    if (!constructor->doesThisDeclarationHaveABody() ||
        constructor->getDefinition() != constructor ||
        !is_in_logical_source(constructor->getLocation())) {
      fail(constructor->getLocation(),
           "the supported constructor must have an inline definition in the selected file");
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
    if (constructor->getNumCtorInitializers() != field_count) {
      fail(constructor->getLocation(),
           "the supported constructor must explicitly initialize every field in declaration order");
      return false;
    }
    std::vector<const clang::CXXCtorInitializer *> source_order(field_count,
                                                                nullptr);
    for (const clang::CXXCtorInitializer *initializer : constructor->inits()) {
      const unsigned order = initializer->getSourceOrder();
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
                           const clang::CXXRecordDecl *record) {
    const auto *prototype =
        destructor->getType()->getAs<clang::FunctionProtoType>();
    if (destructor->getParent()->getCanonicalDecl() !=
            record->getCanonicalDecl() ||
        destructor->getAccess() != clang::AS_public ||
        destructor->isVirtual() || destructor->isDeleted() ||
        prototype == nullptr || !prototype->isNothrow() ||
        prototype->getExceptionSpecType() != clang::EST_BasicNoexcept ||
        !destructor->getExceptionSpecSourceRange().isValid()) {
      fail(destructor->getLocation(),
           "the supported destructor must be public, non-virtual, non-deleted, and explicitly noexcept");
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
    if (body == nullptr || body->body_empty()) {
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
      lowered["span"] = span(field->getSourceRange());
      fields.push_back(std::move(lowered));
    }
    llvm::json::Object result;
    result["declaration_id"] = declaration_id(record);
    result["name"] = record->getNameAsString();
    result["size_bytes"] = static_cast<std::int64_t>(size);
    result["alignment_bytes"] = static_cast<std::int64_t>(alignment);
    result["fields"] = std::move(fields);
    const clang::CXXDestructorDecl *destructor = record->getDestructor();
    if (destructor != nullptr && !destructor->isImplicit()) {
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
    result["span"] = span(record->getSourceRange());
    if (!state_.error.empty()) {
      return std::nullopt;
    }
    return Json(std::move(result));
  }

  std::optional<LoweredMember>
  lower_member(const clang::MemberExpr *member,
               const clang::FunctionDecl *function) {
    const auto *field = llvm::dyn_cast<clang::FieldDecl>(member->getMemberDecl());
    const auto *record = field == nullptr
                             ? nullptr
                             : llvm::dyn_cast<clang::CXXRecordDecl>(
                                   field->getParent()->getDefinition());
    if (field == nullptr || record == nullptr || !remember_record(record)) {
      if (field == nullptr && state_.error.empty()) {
        fail(member->getMemberLoc(),
             "the supported C++ member access must resolve to a data field");
      }
      return std::nullopt;
    }
    const clang::Expr *base = member->getBase()->IgnoreParenImpCasts();
    const auto *this_expression = llvm::dyn_cast<clang::CXXThisExpr>(base);
    const auto *object_method = llvm::dyn_cast<clang::CXXMethodDecl>(function);
    const auto *reference = llvm::dyn_cast<clang::DeclRefExpr>(base);
    const auto *parameter = reference == nullptr
                                ? nullptr
                                : llvm::dyn_cast<clang::ParmVarDecl>(
                                      reference->getDecl());
    const auto *local = reference == nullptr
                            ? nullptr
                            : llvm::dyn_cast<clang::VarDecl>(
                                  reference->getDecl());
    const auto *reference_type =
        parameter == nullptr
            ? nullptr
            : parameter->getType()->getAs<clang::LValueReferenceType>();
    const auto *base_record_type =
        reference_type == nullptr
            ? nullptr
            : reference_type->getPointeeType()->getAs<clang::RecordType>();
    const auto *local_record_type =
        local == nullptr ? nullptr : local->getType()->getAs<clang::RecordType>();
    const bool supported_parameter =
        parameter != nullptr && parameter->getDeclContext() == function &&
        reference_type != nullptr &&
        !reference_type->getPointeeType().isVolatileQualified() &&
        !reference_type->getPointeeType().isRestrictQualified() &&
        base_record_type != nullptr &&
        base_record_type->getDecl()->getCanonicalDecl() ==
            record->getCanonicalDecl();
    const bool supported_local =
        local != nullptr && parameter == nullptr &&
        local->getDeclContext() == function && local->hasLocalStorage() &&
        !local->isStaticLocal() && !local->getType().hasQualifiers() &&
        local_record_type != nullptr &&
        local_record_type->getDecl()->getCanonicalDecl() ==
            record->getCanonicalDecl();
    const bool supported_this =
        this_expression != nullptr && object_method != nullptr &&
        !object_method->isStatic() &&
        object_method->getParent()->getCanonicalDecl() ==
            record->getCanonicalDecl();
    if (member->isArrow() && !supported_this) {
      fail(member->getOperatorLoc(),
           "the first C++ object slice supports arrow access only for the "
           "current method, constructor, or destructor object");
      return std::nullopt;
    }
    if (!supported_parameter && !supported_local && !supported_this) {
      fail(member->getMemberLoc(),
           "supported C++ member access must use the current constructor/destructor object, a mutable record-reference parameter, or a supported record local directly");
      return std::nullopt;
    }
    auto object = lower_place_reference(base, function);
    if (!object) {
      return std::nullopt;
    }
    llvm::json::Object lowered_field;
    lowered_field["record_declaration_id"] = declaration_id(record);
    lowered_field["declaration_id"] = declaration_id(field);
    lowered_field["name"] = field->getNameAsString();
    lowered_field["span"] = span(member->getMemberNameInfo().getSourceRange());
    if (!state_.error.empty()) {
      return std::nullopt;
    }
    return LoweredMember{std::move(*object), Json(std::move(lowered_field))};
  }

  std::optional<Json>
  lower_place_reference(const clang::Expr *expression,
                        const clang::FunctionDecl *expected_function) {
    expression = expression->IgnoreParenImpCasts();
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
      return Json(std::move(result));
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
    if (place == nullptr ||
        (place->getDeclContext() != expected_function &&
         place != active_catch_binding_) ||
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
    return Json(std::move(result));
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

  std::string template_suffix(const clang::FunctionDecl *function) {
    const auto *arguments = function->getTemplateSpecializationArgs();
    if (arguments == nullptr)
      return {};
    std::string suffix;
    for (const auto &argument : arguments->asArray()) {
      if (argument.getKind() == clang::TemplateArgument::Integral &&
          argument.getIntegralType()->isBooleanType()) {
        suffix +=
            argument.getAsIntegral().isZero() ? "__bool_false" : "__bool_true";
      } else if (argument.getKind() == clang::TemplateArgument::Type) {
        const auto type = context_.getCanonicalType(argument.getAsType());
        if (type.hasQualifiers()) {
          fail(function->getLocation(),
               "qualified C++ template type arguments are unsupported");
          return {};
        }
        // Exact builtin identities, rather than widths, keep long and long
        // long (both 64 bits in this profile) separate. Aliases canonicalize.
        const std::pair<clang::QualType, const char *> supported[] = {
            {context_.BoolTy, "__bool"},
            {context_.IntTy, "__int"},
            {context_.UnsignedIntTy, "__unsigned_int"},
            {context_.LongTy, "__long"},
            {context_.UnsignedLongTy, "__unsigned_long"},
            {context_.LongLongTy, "__long_long"},
            {context_.UnsignedLongLongTy, "__unsigned_long_long"}};
        const char *name = nullptr;
        for (const auto &[candidate, token] : supported) {
          if (context_.hasSameType(type, candidate)) {
            name = token;
            break;
          }
        }
        if (name == nullptr) {
          fail(function->getLocation(), "C++ template type arguments require "
                                        "bool or 32/64-bit builtin integers");
          return {};
        }
        suffix += name;
      } else {
        fail(function->getLocation(), "C++ template arguments require Boolean "
                                      "values or supported scalar types");
        return {};
      }
    }
    return suffix;
  }

  std::string function_name(const clang::FunctionDecl *function) {
    std::string name = function->getQualifiedNameAsString();
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
      if (method->getOverloadedOperator() != clang::OO_PlusEqual &&
          method->getOverloadedOperator() != clang::OO_MinusEqual) {
        fail(method->getLocation(), "the supported C++ operator methods are "
                                    "operator+= and operator-= only");
        return {};
      }
      name = method->getOverloadedOperator() == clang::OO_PlusEqual
                 ? "operator_add_assign"
                 : "operator_subtract_assign";
    }
    return method->getParent()->getNameAsString() + "_" + name +
           template_suffix(method);
  }

  std::string constructor_name(
      const clang::CXXConstructorDecl *constructor) const {
    return constructor->getParent()->getNameAsString() + "_constructor";
  }

  std::string destructor_name(
      const clang::CXXDestructorDecl *destructor) const {
    return destructor->getParent()->getNameAsString() + "_destructor";
  }

  Json span(clang::SourceRange range) {
    clang::SourceLocation begin =
        source_manager_.getSpellingLoc(range.getBegin());
    clang::SourceLocation end = source_manager_.getSpellingLoc(range.getEnd());
    if (!begin.isValid() || !end.isValid() || !is_in_logical_source(begin) ||
        !is_in_logical_source(end)) {
      fail(
          begin,
          "the first C++ slice requires source locations in the selected file");
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
    result["file"] = logical_source_;
    result["start_line"] = static_cast<std::int64_t>(start.getLine());
    result["start_column"] = static_cast<std::int64_t>(start.getColumn());
    result["end_line"] = static_cast<std::int64_t>(finish.getLine());
    result["end_column"] = static_cast<std::int64_t>(finish.getColumn());
    return Json(std::move(result));
  }

  Json alias_span(clang::SourceRange range) {
    clang::SourceLocation begin =
        source_manager_.getSpellingLoc(range.getBegin());
    clang::SourceLocation end = source_manager_.getSpellingLoc(range.getEnd());
    if (is_in_logical_source(begin) && is_in_logical_source(end)) {
      return span(range);
    }
    auto dependency = dependency_source(begin);
    auto end_dependency = dependency_source(end);
    if (!dependency || !end_dependency || *dependency != *end_dependency) {
      fail(begin,
           "reachable C++ alias declarations must stay within one declared dependency source");
      return Json(nullptr);
    }
    clang::SourceLocation after = clang::Lexer::getLocForEndOfToken(
        end, 0, source_manager_, context_.getLangOpts());
    const clang::PresumedLoc start = source_manager_.getPresumedLoc(begin);
    const clang::PresumedLoc finish = source_manager_.getPresumedLoc(after);
    if (start.isInvalid() || finish.isInvalid()) {
      fail(begin, "Clang could not resolve an alias declaration span");
      return Json(nullptr);
    }
    dependency_sources_.insert(*dependency);
    llvm::json::Object result;
    result["file"] = *dependency;
    result["start_line"] = static_cast<std::int64_t>(start.getLine());
    result["start_column"] = static_cast<std::int64_t>(start.getColumn());
    result["end_line"] = static_cast<std::int64_t>(finish.getLine());
    result["end_column"] = static_cast<std::int64_t>(finish.getColumn());
    return Json(std::move(result));
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
      const clang::PresumedLoc presumed =
          source_manager_.getPresumedLoc(location);
      if (presumed.isValid()) {
        state_.error = logical_source_ + ":" +
                       std::to_string(presumed.getLine()) + ":" +
                       std::to_string(presumed.getColumn()) +
                       ": error: " + std::move(message);
        return;
      }
    }
    state_.error = logical_source_ + ": error: " + std::move(message);
  }

  clang::ASTContext &context_;
  clang::SourceManager &source_manager_;
  std::string logical_source_;
  std::string logical_source_path_;
  std::string selected_name_;
  std::string dependency_root_;
  std::string compilation_directory_;
  std::string compilation_file_;
  std::vector<std::string> compilation_command_;
  std::string exception_behavior_;
  const clang::VarDecl *active_catch_binding_ = nullptr;
  ExportState &state_;
  std::vector<clang::FunctionDecl *> matches_;
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
  ExportConsumer(clang::ASTContext &context, const Options &options,
                 ExportState &state)
      : exporter_(context, options.logical_source, options.logical_source_path,
                  options.function, options.dependency_root,
                  options.compilation_directory, options.compilation_file,
                  options.compilation_command, options.exception_behavior,
                  state) {}

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

  std::unique_ptr<clang::ASTConsumer>
  CreateASTConsumer(clang::CompilerInstance &compiler,
                    llvm::StringRef) override {
    compiler.getPreprocessor().addPPCallbacks(
        std::make_unique<PreprocessorFiles>(compiler.getSourceManager(),
                                            options_.compilation_directory,
                                            state_));
    return std::make_unique<ExportConsumer>(compiler.getASTContext(), options_,
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
