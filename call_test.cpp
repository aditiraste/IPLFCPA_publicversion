#include "myHeader.h"

int *x, *y, u, v;

void fun() {
	x = &u;
}

int main() {

	x = &v;
	fun();
	y = x;
	return *y;
}
