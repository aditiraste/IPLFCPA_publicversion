int *x,*y,*z,u,v;

void fun(int *a) {
    y = a;
}

int main() {
    x = &v;
    fun(x);
    return *y;
}