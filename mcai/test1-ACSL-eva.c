#include "__fc_builtin.h"
#include "limits.h"

int main() {
  int x = 0;
Frama_C_dump_each(); __FRAMAC_OCTAGON0:;
  int n = Frama_C_interval(100, 1000000);
  int y = n;
  int runtime_div;
Frama_C_dump_each(); __FRAMAC_OCTAGON1:;
  while (x + y <= 999999) {
Frama_C_dump_each();   __FRAMAC_OCTAGON2:;
    x++;
    y--;
  // Frama_C_dump_each();
Frama_C_dump_each();   __FRAMAC_OCTAGON:;
    // Check n-y > 0 using octagon domain.
    /*@ assert n-y > 0; */
    __VERIFIER_assert(n - y > 0);
    runtime_div = x / (n - y);
  }
Frama_C_dump_each(); __FRAMAC_OCTAGON4:;
}
