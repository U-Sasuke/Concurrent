package com.example.test.concurrent.aqs;

import java.util.concurrent.locks.AbstractQueuedSynchronizer;

/**
 * @describtion
 * @creator yaoqing
 * @date 2019-10-17
 */
public class MySharedLock {

    public MySharedLock(int permits) {
        myAQS = new MyAbstractQueuedSynchronize(permits);
    }

    private final MyAbstractQueuedSynchronize myAQS;

    static class MyAbstractQueuedSynchronize extends AbstractQueuedSynchronizer {

        public MyAbstractQueuedSynchronize(int permits) {
            setState(permits);
        }

        @Override
        protected final int tryAcquireShared(int arg) {
            for (; ; ) {
                int state = getState();
                int count = state - arg;
                if (count >= 0 && compareAndSetState(state, count)) {
                    return count;
                }
                if (count < 0) {
                    return count;
                }
            }
        }

        @Override
        protected final boolean tryReleaseShared(int arg) {
            for (; ; ) {
                int state = getState();
                int count = state + arg;
                if (count >= 0 && compareAndSetState(state, count)) {
                    return true;
                }
                if (count < 0) {
                    return false;
                }
            }
        }

        @Override
        protected final boolean isHeldExclusively() {
            return getExclusiveOwnerThread() == Thread.currentThread();
        }
    }

    public void acquire() {
        myAQS.acquireShared(1);
    }

    public void release() {
        myAQS.releaseShared(1);
    }

    public static void main(String[] args) {
        MySharedLock mySharedLock = new MySharedLock(2);
        Runnable runnable = () -> {
            System.out.println(Thread.currentThread().getName() + " : 尝试获取凭证");
            mySharedLock.acquire();
            System.out.println(Thread.currentThread().getName() + " : 成功获取");
            try {
                Thread.sleep(2000);
            } catch (InterruptedException e) {
                e.printStackTrace();
            }
            System.out.println(Thread.currentThread().getName() + " : 处理完事情，释放凭证");
            mySharedLock.release();

        };
        for (int i = 0; i < 5; i++) {
            new Thread(runnable).start();
        }
    }

}

/**
 Result:
 Thread-0 : 尝试获取凭证
 Thread-0 : 成功获取
 Thread-2 : 尝试获取凭证
 Thread-2 : 成功获取
 Thread-1 : 尝试获取凭证
 Thread-4 : 尝试获取凭证
 Thread-3 : 尝试获取凭证
 Thread-2 : 处理完事情，释放凭证
 Thread-0 : 处理完事情，释放凭证
 Thread-1 : 成功获取
 Thread-4 : 成功获取
 Thread-4 : 处理完事情，释放凭证
 Thread-1 : 处理完事情，释放凭证
 Thread-3 : 成功获取
 Thread-3 : 处理完事情，释放凭证
 */
