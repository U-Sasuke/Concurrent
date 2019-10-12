package com.example.test.concurrent;

import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;

/**
 * @describtion
 * @creator yaoqing
 * @date 2019-10-11
 */
public class ThreadPoolExecutorTest {

//    private static ExecutorService executor = Executors.newFixedThreadPool(2);
//
//
//    @Override
//    public void run() {
//        System.out.println("线程启动：" + Thread.currentThread().getName());
//        try {
//            Thread.sleep(1000000);
//        } catch (Exception e) {
//        }
//    }

    public static void main(String[] args) {
        int a = 5, b = 6;
        while (b != 0) {
            String astr = Integer.toBinaryString(a);
            String bstr = Integer.toBinaryString(b);
            int _a = a ^ b;
            String astra = Integer.toBinaryString(_a);
            int _b = _a^b;
            String bstrb = Integer.toBinaryString(_b);
            b = _b;
        }
        System.out.printf(a + "");

    }

}
