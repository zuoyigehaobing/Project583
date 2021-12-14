#include <limits.h>

int divide(int dividend, int divisor) {
    if( dividend == 0 )
        return 0;

    if( divisor == 1 )
        return dividend;

    if( divisor == -1 && dividend == INT_MIN )
        return INT_MAX;

    if( divisor == -1 )
        return -dividend;

    if( divisor == INT_MIN && dividend == INT_MIN )
        return 1;

    if( divisor == INT_MIN )
        return 0;

    bool ispos = true;
    if(divisor < 0 && dividend > 0 || divisor > 0 && dividend < 0)
        ispos = false;

    if(divisor < 0)
        divisor = -divisor;

    int extra = 0;
    if(dividend == INT_MIN) {
        dividend = INT_MAX;
        extra = 1;
    }

    if(dividend < 0)
        dividend = -dividend;

    if(dividend < divisor-extra)
        return 0;

    int quotient = 1;
    dividend -= divisor - extra;
    while(divisor <= dividend) {
        int mul = 1;
        int accum = divisor;

        while(accum <= dividend - accum) {
            accum <<=1;
            mul <<=1;
        }

        dividend -= accum;
        quotient +=mul;
    }

    return ispos ? quotient :-quotient;
}

int main() {
  int a = 123456;
  int b = 12;
  int res = divide(a,b);
  return 0;
}
