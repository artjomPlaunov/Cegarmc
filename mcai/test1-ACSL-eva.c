#include "__fc_builtin.h"
#include "limits.h"

int main () {
    int x = 0;
    int n = Frama_C_interval(100,1000000);
    int y = n;
    int runtime_div;
    
    while (x+y <= 999999) {
        x++;
        y--;
        //Frama_C_dump_each();
Frama_C_dump_each();
        __FRAMAC_OCTAGON: 
        // Check n-y > 0 using octagon domain.
        /*@ assert n-y > 0; */
        runtime_div = x/(n-y);
        
    }
    
}
