package com.example.test.concurrent.thread;

import java.util.ArrayList;
import java.util.List;
import java.util.concurrent.locks.ReentrantLock;

public class MyTest {

    public static void main(String[] args) {
        List<Goods> goods = new ArrayList<>();
        for (int i = 1; i < 4; i++) {
            Goods good = new Goods();
            good.goodsId = "good-" + i;
            goods.add(good);
        }
        List<String> userIds = new ArrayList<>();
        for (int i = 1; i < 100; i++) {
            userIds.add("user-" + i);
        }
        SecKill secKill = new SecKillImpl();
        secKill.simulate(goods, userIds);
    }

    public static class Goods {
        String goodsId;
        String buyerId;

        @Override
        public String toString() {
            return " 商品ID:" + goodsId + " 用户ID：" + buyerId;
        }
    }

    public static class Result {
        List<Goods> goodsList;
        Long elapsedTime;

        @Override
        public String toString() {
            return goodsList.toString() + "耗时：" + elapsedTime + "毫秒！";
        }
    }

    public interface SecKill {
        Result simulate(List<Goods> goods, List<String> userIds);
    }

    public static class SecKillImpl implements MyTest.SecKill {
        private List<Goods> killGoods;
        private volatile int count;
        private ReentrantLock lock = new ReentrantLock();

        @Override
        public Result simulate(List<Goods> goods, List<String> userIds) {
            killGoods = goods;
            count = goods.size();
            long start = System.currentTimeMillis();
            for (String userId : userIds) {
                new Thread(() -> getGood(userId)).start();
            }
            if (count > 0) {
                Thread.yield();
            }
            Result result = new Result();
            result.goodsList = killGoods;
            result.elapsedTime = System.currentTimeMillis() - start;
            System.out.println(result.toString());
            return result;
        }

        private void getGood(String userId) {
            for (; ; ) {
                if (count <= 0) {
                    return;
                } else {
                    if (lock.tryLock()) {
                        count--;
                        if (count < 0) {
                            lock.unlock();
                            return;
                        }
                        killGoods.get(count).buyerId = userId;
                        System.out.println(userId + "，恭喜你抢到了!");
                        lock.unlock();
                        return;
                    }
                }
            }
        }
    }

}
