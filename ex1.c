#include <stdio.h>

void f(int** x, int** y){
    int* temp;
    temp = *x; //** (&x)
    *x = *y;
    *y = temp;
}


int main(int argc, char* argv[]){
    int a = 4;
    int b = 5;
    int *c = &a;
    int *d;
    

	f(&c, &d);
	
	d = c;

	return 1;
}
