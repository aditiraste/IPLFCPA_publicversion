
/* Case 1: Working as on 27.4.22*/
int *x, *y, *z, u;

int* fun(int* a) {
	y = a;
	return y;
}

int main() {
	int c;
	x = &c;
	z = fun(x);
	return *z;
}


