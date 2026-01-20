class Loop {
    void test() {
        int g;
        float h = 1;
        int a = g;     // 常量传播
        int b = a;     // a 的值传播
        char c = 'c';
        int d = 0;
        C obj = new C();
        d = obj.f;     // NAC
        int e = obj.m();// NAC
        obj.f = 5;     // 恒等函数处理
    }
}