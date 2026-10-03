int echo(long x) noexcept { return 7; }
int echo(long long x) noexcept { return 9; }
namespace A {
int same(int x) noexcept { return 11; }
struct H { static int same(int x) noexcept { return 13; } };
}
int A_same(int x) noexcept { return 17; }
namespace B {
struct H { static int same(int x) noexcept { return 19; } };
}
int relay(long x, long long y, int z) noexcept {
  int a = echo(x);
  int b = echo(y);
  int c = A::same(z);
  int d = A_same(z);
  int e = A::H::same(z);
  int f = B::H::same(z);
  return a + b + c + d + e + f;
}
