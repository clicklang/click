static inline int helper(void) { return 1; }
int first_use(void) { return helper(); }
