#include "__fc_builtin.h"
#include "limits.h"

int main () {
    int x = 0;
    int n = Frama_C_interval(100,1000000);
    int y = n;
    int runtime_div;
    __FRAMAC_OCTAGON1: ;
    while (x+y <= 999999) {
        __FRAMAC_OCTAGON2: ;
        x++;
        y--;
        //Frama_C_dump_each();
        __FRAMAC_OCTAGON3: ;
        // Check n-y > 0 using octagon domain.
        /*@ assert n-y > 0; */
        runtime_div = x/(n-y);
    }
    __FRAMAC_OCTAGON4: ;

}
