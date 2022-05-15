
int *x, *y, u;

void fun(int *a) {
 x = a;
}

void (*fp)(int*);

int main() {
	y = &u;
	fp = fun;
	(*fp)(y);
	return *x;
}

/*#include<stdio.h>
int *x, *y, u, v;

void fun(int *a) {
 x = a;
}

void fun1(int *b) {
 x = b;
}

void (*fp)(int*);

int main() {
	u = 10; v =20;
	y = &u;
	fp = fun;
	(*fp)(y);
	printf("\nx = %d", *x);
	y = &v;
	fp = fun1;
	(*fp)(y);
	printf("\nx = %d", *x);
	
	return *x;
}*/
