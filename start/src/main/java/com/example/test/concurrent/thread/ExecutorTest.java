package com.example.test.concurrent.thread;

import java.util.concurrent.*;

public class ExecutorTest {

    public static class MyPolicy implements RejectedExecutionHandler {
        public MyPolicy() {
        }

        public void rejectedExecution(Runnable r, ThreadPoolExecutor e) {
            System.out.println("线程池满了，别晃（放）了。。。");
        }
    }

    public static class MyRunnable implements Runnable {
        int count;

        public MyRunnable(int count) {
            this.count = count;
        }

        @Override
        public void run() {
            System.out.println(Thread.currentThread().getName() + " : 执行任务" + count);
            try {
                Thread.sleep(500);
            } catch (InterruptedException e) {
                e.printStackTrace();
            }
        }
    }

    public static void main(String[] args) {
        RejectedExecutionHandler myHandler = new MyPolicy();
        ExecutorService executor = new ThreadPoolExecutor(2, 2,
                0L, TimeUnit.MILLISECONDS,
                new LinkedBlockingQueue<Runnable>(3), myHandler);
        for (int i = 0; i < 10; i++) {
            System.out.println("提交任务" + i);
            executor.submit(new MyRunnable(i));
            try {
                Thread.sleep(100);
            } catch (InterruptedException e) {
                e.printStackTrace();
            }
        }
    }

}
