# 0 "label_fit.c"
# 0 "<built-in>"
# 0 "<command-line>"
# 1 "label_fit.c"
# 1 "include/label_config.h" 1
# 2 "label_fit.c" 2
# 1 "label.h" 1



unsigned long label_fit(unsigned long length);
unsigned long label_measure(const char *src);
unsigned long label_copy(char *dst, const char *src);
# 3 "label_fit.c" 2


unsigned long label_fit(unsigned long length)
{
 if (length >= 32)
  return 32 - 1;
 return length;
}
