class A {
    int f;
    public static void main(String[] args) {
        A a = new A();
        A b = a;

        int x = 1;
        a.f = x;

        x = 2;

        int y = b.f;
    }
}
