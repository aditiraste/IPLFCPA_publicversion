

/* case 1:
int *x, *y, *z, u, v;

void fun() {
	x = &u;
}

int main() {

	x = &v;
	fun();
	y = x;
	return *y;
}*/

//case 2
int *x, *y, *z, u, v;

void fun() {
	x = z;
}

int main() {

	z = &v;
	fun();
	y = x;
	return *y;
}

