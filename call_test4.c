
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



// Index: 1	 Lhs: <y, 1 > 		 Rhs: <a, 1>
// Index: 2	 Lhs: <i1, 1 > 		 Rhs: <y, 1>
// Index: 3 Rhs: <i1, 1>

// Index: 4	 Lhs: <x, 1 > 		 Rhs: <c, 0>
// Index: 5	 Lhs: <i, 1 > 		 Rhs: <x, 1>

// Index: 6	 Lhs: <a, 1 > 		 Rhs: <i, 1>
// Index: 7 Rhs: <fun, 1>
// Index: 8	 Lhs: <call, 1 > 		 Rhs: <i1, 1>

// Index: 9	 Lhs: <z, 1 > 		 Rhs: <call, 1>
// Index: 10 Rhs: <z, 1>


