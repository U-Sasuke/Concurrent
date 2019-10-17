package com.example.test.concurrent.binary;

public class BitOperationTest {

    public static void main(String[] args) {
        int a = 13, b = 6;
        System.out.println("   a    ：" + getBinaryStr(a));
        System.out.println("   b    ：" + getBinaryStr(b));
        System.out.println("  a&b   ：" + getBinaryStr(a & b));
        System.out.println("  a|b   ：" + getBinaryStr(a | b));
        System.out.println("   ~a   ：" + getBinaryStr(~a));
        System.out.println("  a^b   ：" + getBinaryStr(a ^ b));
        System.out.println("  a<<2  ：" + getBinaryStr(a << 2));
        System.out.println("   -a   ：" + getBinaryStr(-a));
        System.out.println("  a>>2  ：" + getBinaryStr(a >> 2));
        System.out.println("(-a)>>2 ：" + getBinaryStr((-a) >> 2));
        System.out.println("  a>>>2 ：" + getBinaryStr(a >>> 2));
        System.out.println("(-a)>>>2：" + getBinaryStr((-a) >>> 2));
    }

    private static String getBinaryStr(int n) {
        StringBuilder str = new StringBuilder(Integer.toBinaryString(n));
        int len = str.length();
        if (len < 32) {
            for (int i = 0; i < 32 - len; i++) {
                str.insert(0, "0");
            }
        }
        return str.substring(0, 8) + " " + str.substring(8, 16) + " " + str.substring(16, 24) + " " + str.substring(24, 32);
    }
}
