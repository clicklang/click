# An unsigned literal in a failed claim is printed as negative

Soundness: not soundness. A refused claim is reported with a different
number than the one written, which misleads; nothing false is accepted.

A diagnostic must echo the claim as written. A `uint32` literal above
`2^31` in a refused `ensures` is printed as its signed reinterpretation.

Reproduced on master `6f16a4a8`:

```c
#include <stdint.h>
uint32_t big(void) { return 1u; }
```

```click
verifying "big.c";
uint32 big() { ensures result == 2707161783u32 by auto; }
```

The refusal reads `ensures result == -1587805513u32` failed ... right side
evaluated to 2707161783u32`. The label shows `-1587805513u32` (the same bits
read as `int32`) although the source and the evaluated right side say
`2707161783u32`.

Acceptance: the refused claim's label prints `2707161783u32`, and a regression
pins the spelling of an unsigned literal at and above `2^31`.
