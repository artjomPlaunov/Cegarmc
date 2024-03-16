extern void abort(void);
void __VERIFIER_assert(int cond) {
  if (!(cond)) {
  ERROR : { abort(); }
  }
}
extern int __VERIFIER_nondet_int(void);
extern void __VERIFIER_assume(int);
#include "limits.h"

int main() {
  int x = 0;
__FRAMAC_OCTAGON0:;
  int n = __VERIFIER_nondet_int();
  if (n < 100 || n > 1000000)
    abort();
  int y = n;
  int runtime_div;
__FRAMAC_OCTAGON1:;
  __VERIFIER_assume(n - y == 0);
  while (x + y <= 999999) {
  __FRAMAC_OCTAGON2:;
    __VERIFIER_assume(0 <= n - y && n - y <= INT_MAX);
    __VERIFIER_assume(99 <= x + y && x + y <= 999999);
    __VERIFIER_assume(99 <= x + n && x + n <= INT_MAX);
    x++;
    y--;
  // Frama_C_dump_each();
  __FRAMAC_OCTAGON:;
    __VERIFIER_assume(1 <= n - y && n - y <= INT_MAX);
    __VERIFIER_assume(99 <= x + y && x + y <= 999999);
    __VERIFIER_assume(100 <= x + n && x + n <= INT_MAX);
    // Check n-y > 0 using octagon domain.
    /*@ assert n-y > 0; */
    __VERIFIER_assert(n - y > 0);
    runtime_div = x / (n - y);
  }
__FRAMAC_OCTAGON4:;
  __VERIFIER_assume(0 <= n - y && n - y <= INT_MAX);
  __VERIFIER_assume(x + y == 1000000 || x + y == 1000001);
  __VERIFIER_assume(1000000 <= x + n && x + n <= INT_MAX);
}
