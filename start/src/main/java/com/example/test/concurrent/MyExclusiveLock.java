package com.example.test.concurrent;

import java.util.concurrent.TimeUnit;
import java.util.concurrent.locks.AbstractQueuedSynchronizer;
import java.util.concurrent.locks.Condition;
import java.util.concurrent.locks.Lock;

/**
 * @describtion
 * @creator yaoqing
 * @date 2019-10-17
 */
public class MyExclusiveLock implements Lock {

    public MyExclusiveLock() {
        myAQS = new MyAbstractQueuedSynchronize();
    }

    private final MyAbstractQueuedSynchronize myAQS;

    static class MyAbstractQueuedSynchronize extends AbstractQueuedSynchronizer {

        @Override
        protected final boolean tryAcquire(int arg) {
            int state = getState();
            if (state == 0 && compareAndSetState(0, 1)) {
                setExclusiveOwnerThread(Thread.currentThread());
                return true;
            } else {
                return false;
            }
        }

        @Override
        protected final boolean tryRelease(int arg) {
            setState(0);
            setExclusiveOwnerThread(null);
            return true;
        }

        @Override
        protected final boolean isHeldExclusively() {
            return getExclusiveOwnerThread() == Thread.currentThread();
        }
    }

    @Override
    public void lock() {
        myAQS.acquire(1);
    }

    @Override
    public void lockInterruptibly() throws InterruptedException {

    }

    @Override
    public boolean tryLock() {
        return myAQS.tryAcquire(1);
    }

    @Override
    public boolean tryLock(long time, TimeUnit unit) throws InterruptedException {
        return false;
    }

    @Override
    public void unlock() {
        myAQS.release(1);
    }

    @Override
    public Condition newCondition() {
        return myAQS.new ConditionObject();
    }

    public static void main(String[] args) throws InterruptedException {
        MyExclusiveLock myExclusiveLock = new MyExclusiveLock();
        Condition condition = myExclusiveLock.newCondition();
        Runnable runnableAwait = () -> {
            System.out.println(Thread.currentThread().getName() + " : 尝试获取锁");
            myExclusiveLock.lock();
            System.out.println(Thread.currentThread().getName() + " : 获取锁成功");
            try {
                Thread.sleep(500);
                System.out.println(Thread.currentThread().getName() + " : 进入等待，并释放锁");
                condition.await();
                System.out.println(Thread.currentThread().getName() + " : 被唤醒了！并获取锁");
            } catch (InterruptedException e) {
                e.printStackTrace();
            } finally {
                myExclusiveLock.unlock();
                System.out.println(Thread.currentThread().getName() + " : 释放锁");
            }
        };
        Runnable runnableSignal = () -> {
            System.out.println(Thread.currentThread().getName() + " : 尝试获取锁");
            myExclusiveLock.lock();
            System.out.println(Thread.currentThread().getName() + " : 获取锁成功");
            condition.signal();
            System.out.println(Thread.currentThread().getName() + " : 唤醒等待队列首节点线程");
            myExclusiveLock.unlock();
            System.out.println(Thread.currentThread().getName() + " : 释放锁");
        };
        new Thread(runnableAwait).start();
        new Thread(runnableAwait).start();
        new Thread(runnableSignal).start();
        new Thread(runnableSignal).start();
    }

}

/**
 Result:
 Thread-0 : 尝试获取锁
 Thread-2 : 尝试获取锁
 Thread-1 : 尝试获取锁
 Thread-3 : 尝试获取锁
 Thread-0 : 获取锁成功
 Thread-0 : 进入等待，并释放锁
 Thread-2 : 获取锁成功
 Thread-2 : 唤醒等待队列首节点线程
 Thread-2 : 释放锁
 Thread-1 : 获取锁成功
 Thread-1 : 进入等待，并释放锁
 Thread-3 : 获取锁成功
 Thread-3 : 唤醒等待队列首节点线程
 Thread-3 : 释放锁
 Thread-0 : 被唤醒了！并获取锁
 Thread-0 : 释放锁
 Thread-1 : 被唤醒了！并获取锁
 Thread-1 : 释放锁
 */
