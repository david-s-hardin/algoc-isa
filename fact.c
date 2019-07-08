#include <stdio.h>

unsigned long fact(unsigned long num, unsigned long acc) {
    if (num < 2) {
        return acc;
    } else {
        return fact(num - 1, acc * num);
    }
}


int main(int argc, char **argv) {
  unsigned long num = 0;
  unsigned long res = 0;

  for (unsigned long i = num; i <= 20; i++) {
    res = fact(i, 1);
  
    printf("fact(%ld) = %ld\n", i, res);
  }
}

