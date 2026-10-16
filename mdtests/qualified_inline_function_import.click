verifying "qualified_inline_function_first.c" as selected;
int32 selected::helper() { ensures result == 1; } by { execute(); simp(); }
