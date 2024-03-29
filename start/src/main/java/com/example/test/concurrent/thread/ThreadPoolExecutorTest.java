//package com.example.test.concurrent.thread;
//
//import java.security.AccessControlContext;
//import java.security.AccessController;
//import java.security.PrivilegedAction;
//import java.util.concurrent.*;
//import java.util.concurrent.locks.AbstractQueuedSynchronizer;
//import java.util.concurrent.locks.Condition;
//import java.util.concurrent.locks.ReentrantLock;
//import java.util.concurrent.atomic.AtomicInteger;
//import java.util.*;
//
//public class ThreadPoolExecutorTest extends AbstractExecutorService {
//
//   /** 线程池状态+线程数，int是32位，高3位保存运行状态，低29位保存线程数量
//       值为 11100000 00000000 00000000 00000000 */
//    private final AtomicInteger ctl = new AtomicInteger(ctlOf(RUNNING, 0));
//
//    /** 线程数量位数：29 */
//    private static final int COUNT_BITS = Integer.SIZE - 3;
//
//    /** 线程数量容量：00011111 11111111 11111111 11111111 */
//    private static final int CAPACITY   = (1 << COUNT_BITS) - 1;
//
//    /** 线程状态：运行中 11100000 00000000 00000000 00000000  */
//    private static final int RUNNING    = -1 << COUNT_BITS;
//
//    /** 线程状态：关闭 00000000 00000000 00000000 00000000  */
//    private static final int SHUTDOWN   =  0 << COUNT_BITS;
//
//    /** 线程状态：停止 00100000 00000000 00000000 00000000  */
//    private static final int STOP       =  1 << COUNT_BITS;
//
//    /** 线程状态：整理 01000000 00000000 00000000 00000000  */
//    private static final int TIDYING    =  2 << COUNT_BITS;
//
//    /** 线程状态：终止 01100000 00000000 00000000 00000000  */
//    private static final int TERMINATED =  3 << COUNT_BITS;
//
//    /** 获取运行状态(获取高3位) */
//    private static int runStateOf(int c)     { return c & ~CAPACITY; }
//
//    /** 获取线程数量(获取低29位) */
//    private static int workerCountOf(int c)  { return c & CAPACITY; }
//
//    private static int ctlOf(int rs, int wc) { return rs | wc; }
//
//    /*
//     * Bit field accessors that don't require unpacking ctl.
//     * These depend on the bit layout and on workerCount being never negative.
//     */
//
//    private static boolean runStateLessThan(int c, int s) {
//        return c < s;
//    }
//
//    private static boolean runStateAtLeast(int c, int s) {
//        return c >= s;
//    }
//
//    private static boolean isRunning(int c) {
//        return c < SHUTDOWN;
//    }
//
//    /**
//     * Attempts to CAS-increment the workerCount field of ctl.
//     */
//    private boolean compareAndIncrementWorkerCount(int expect) {
//        return ctl.compareAndSet(expect, expect + 1);
//    }
//
//    /**
//     * Attempts to CAS-decrement the workerCount field of ctl.
//     */
//    private boolean compareAndDecrementWorkerCount(int expect) {
//        return ctl.compareAndSet(expect, expect - 1);
//    }
//
//    /**
//     * Decrements the workerCount field of ctl. This is called only on
//     * abrupt termination of a thread (see processWorkerExit). Other
//     * decrements are performed within getTask.
//     */
//    private void decrementWorkerCount() {
//        do {} while (! compareAndDecrementWorkerCount(ctl.get()));
//    }
//
//    /** 阻塞队列 */
//    private final BlockingQueue<Runnable> workQueue;
//
//    /** 全局锁 */
//    private final ReentrantLock mainLock = new ReentrantLock();
//
//    /** 工作线程集合，操作之前需要获取全局锁 */
//    private final HashSet<Worker> workers = new HashSet<Worker>();
//
//    private final Condition termination = mainLock.newCondition();
//
//    /** 线程池的最大容量 */
//    private int largestPoolSize;
//
//    /** 已完成的任务数量 */
//    private long completedTaskCount;
//
//    /** 线程工厂 */
//    private volatile ThreadFactory threadFactory;
//
//    /** 拒绝策略handler */
//    private volatile RejectedExecutionHandler handler;
//
//    /** 超出核心线程数时线程的保活时间 */
//    private volatile long keepAliveTime;
//
//    /** 允许核心线程超时标识 */
//    private volatile boolean allowCoreThreadTimeOut;
//
//    /** 核心线程数 */
//    private volatile int corePoolSize;
//
//    /** 最大线程数 */
//    private volatile int maximumPoolSize;
//
//    /** 默认拒绝策略：直接抛出异常策略 */
//    private static final RejectedExecutionHandler defaultHandler =
//            new AbortPolicy();
//
//    /**
//     * Permission required for callers of shutdown and shutdownNow.
//     * We additionally require (see checkShutdownAccess) that callers
//     * have permission to actually interrupt threads in the worker set
//     * (as governed by Thread.interrupt, which relies on
//     * ThreadGroup.checkAccess, which in turn relies on
//     * SecurityManager.checkAccess). Shutdowns are attempted only if
//     * these checks pass.
//     *
//     * All actual invocations of Thread.interrupt (see
//     * interruptIdleWorkers and interruptWorkers) ignore
//     * SecurityExceptions, meaning that the attempted interrupts
//     * silently fail. In the case of shutdown, they should not fail
//     * unless the SecurityManager has inconsistent policies, sometimes
//     * allowing access to a thread and sometimes not. In such cases,
//     * failure to actually interrupt threads may disable or delay full
//     * termination. Other uses of interruptIdleWorkers are advisory,
//     * and failure to actually interrupt will merely delay response to
//     * configuration changes so is not handled exceptionally.
//     */
//    private static final RuntimePermission shutdownPerm =
//            new RuntimePermission("modifyThread");
//
//    /* The context to be used when executing the finalizer, or null. */
//    private final AccessControlContext acc;
//
//    /**
//     * Class Worker mainly maintains interrupt control state for
//     * threads running tasks, along with other minor bookkeeping.
//     * This class opportunistically extends AbstractQueuedSynchronizer
//     * to simplify acquiring and releasing a lock surrounding each
//     * task execution.  This protects against interrupts that are
//     * intended to wake up a worker thread waiting for a task from
//     * instead interrupting a task being run.  We implement a simple
//     * non-reentrant mutual exclusion lock rather than use
//     * ReentrantLock because we do not want worker tasks to be able to
//     * reacquire the lock when they invoke pool control methods like
//     * setCorePoolSize.  Additionally, to suppress interrupts until
//     * the thread actually starts running tasks, we initialize lock
//     * state to a negative value, and clear it upon start (in
//     * runWorker).
//     */
//    private final class Worker
//            extends AbstractQueuedSynchronizer
//            implements Runnable
//    {
//
//        private static final long serialVersionUID = 6138294804551838833L;
//
//        /** 执行任务的线程 */
//        final Thread thread;
//
//        /** 需要执行的任务 */
//        Runnable firstTask;
//
//        /** 执行完成的任务数 */
//        volatile long completedTasks;
//
//        Worker(Runnable firstTask) {
//            /** 防止任务在执行前被中断 */
//            setState(-1);
//            this.firstTask = firstTask;
//            this.thread = getThreadFactory().newThread(this);
//        }
//
//        /** 运行的run方法 */
//        public void run() {
//            runWorker(this);
//        }
//
//        protected boolean isHeldExclusively() {
//            return getState() != 0;
//        }
//
//        protected boolean tryAcquire(int unused) {
//            if (compareAndSetState(0, 1)) {
//                setExclusiveOwnerThread(Thread.currentThread());
//                return true;
//            }
//            return false;
//        }
//
//        protected boolean tryRelease(int unused) {
//            setExclusiveOwnerThread(null);
//            setState(0);
//            return true;
//        }
//
//        public void lock()        { acquire(1); }
//        public boolean tryLock()  { return tryAcquire(1); }
//        public void unlock()      { release(1); }
//        public boolean isLocked() { return isHeldExclusively(); }
//
//        void interruptIfStarted() {
//            Thread t;
//            if (getState() >= 0 && (t = thread) != null && !t.isInterrupted()) {
//                try {
//                    t.interrupt();
//                } catch (SecurityException ignore) {
//                }
//            }
//        }
//    }
//
//    /*
//     * Methods for setting control state
//     */
//
//    /**
//     * Transitions runState to given target, or leaves it alone if
//     * already at least the given target.
//     *
//     * @param targetState the desired state, either SHUTDOWN or STOP
//     *        (but not TIDYING or TERMINATED -- use tryTerminate for that)
//     */
//    private void advanceRunState(int targetState) {
//        for (;;) {
//            int c = ctl.get();
//            if (runStateAtLeast(c, targetState) ||
//                    ctl.compareAndSet(c, ctlOf(targetState, workerCountOf(c))))
//                break;
//        }
//    }
//
//    /**
//     * Transitions to TERMINATED state if either (SHUTDOWN and pool
//     * and queue empty) or (STOP and pool empty).  If otherwise
//     * eligible to terminate but workerCount is nonzero, interrupts an
//     * idle worker to ensure that shutdown signals propagate. This
//     * method must be called following any action that might make
//     * termination possible -- reducing worker count or removing tasks
//     * from the queue during shutdown. The method is non-private to
//     * allow access from ScheduledThreadPoolExecutor.
//     */
//    final void tryTerminate() {
//        for (;;) {
//            int c = ctl.get();
//            if (isRunning(c) ||
//                    runStateAtLeast(c, TIDYING) ||
//                    (runStateOf(c) == SHUTDOWN && ! workQueue.isEmpty()))
//                return;
//            if (workerCountOf(c) != 0) { // Eligible to terminate
//                interruptIdleWorkers(ONLY_ONE);
//                return;
//            }
//
//            final ReentrantLock mainLock = this.mainLock;
//            mainLock.lock();
//            try {
//                if (ctl.compareAndSet(c, ctlOf(TIDYING, 0))) {
//                    try {
//                        terminated();
//                    } finally {
//                        ctl.set(ctlOf(TERMINATED, 0));
//                        termination.signalAll();
//                    }
//                    return;
//                }
//            } finally {
//                mainLock.unlock();
//            }
//            // else retry on failed CAS
//        }
//    }
//
//    /*
//     * Methods for controlling interrupts to worker threads.
//     */
//
//    /**  */
//    private void checkShutdownAccess() {
//        SecurityManager security = System.getSecurityManager();
//        if (security != null) {
//            security.checkPermission(shutdownPerm);
//            final ReentrantLock mainLock = this.mainLock;
//            mainLock.lock();
//            try {
//                for (Worker w : workers)
//                    security.checkAccess(w.thread);
//            } finally {
//                mainLock.unlock();
//            }
//        }
//    }
//
//    /**
//     * Interrupts all threads, even if active. Ignores SecurityExceptions
//     * (in which case some threads may remain uninterrupted).
//     */
//    private void interruptWorkers() {
//        final ReentrantLock mainLock = this.mainLock;
//        mainLock.lock();
//        try {
//            for (Worker w : workers)
//                w.interruptIfStarted();
//        } finally {
//            mainLock.unlock();
//        }
//    }
//
//    /**
//     * Interrupts threads that might be waiting for tasks (as
//     * indicated by not being locked) so they can check for
//     * termination or configuration changes. Ignores
//     * SecurityExceptions (in which case some threads may remain
//     * uninterrupted).
//     *
//     * @param onlyOne If true, interrupt at most one worker. This is
//     * called only from tryTerminate when termination is otherwise
//     * enabled but there are still other workers.  In this case, at
//     * most one waiting worker is interrupted to propagate shutdown
//     * signals in case all threads are currently waiting.
//     * Interrupting any arbitrary thread ensures that newly arriving
//     * workers since shutdown began will also eventually exit.
//     * To guarantee eventual termination, it suffices to always
//     * interrupt only one idle worker, but shutdown() interrupts all
//     * idle workers so that redundant workers exit promptly, not
//     * waiting for a straggler task to finish.
//     */
//    private void interruptIdleWorkers(boolean onlyOne) {
//        final ReentrantLock mainLock = this.mainLock;
//        mainLock.lock();
//        try {
//            for (Worker w : workers) {
//                Thread t = w.thread;
//                if (!t.isInterrupted() && w.tryLock()) {
//                    try {
//                        t.interrupt();
//                    } catch (SecurityException ignore) {
//                    } finally {
//                        w.unlock();
//                    }
//                }
//                if (onlyOne)
//                    break;
//            }
//        } finally {
//            mainLock.unlock();
//        }
//    }
//
//    /**
//     * Common form of interruptIdleWorkers, to avoid having to
//     * remember what the boolean argument means.
//     */
//    private void interruptIdleWorkers() {
//        interruptIdleWorkers(false);
//    }
//
//    private static final boolean ONLY_ONE = true;
//
//    /*
//     * Misc utilities, most of which are also exported to
//     * ScheduledThreadPoolExecutor
//     */
//
//    /**
//     * Invokes the rejected execution handler for the given command.
//     * Package-protected for use by ScheduledThreadPoolExecutor.
//     */
//    final void reject(Runnable command) {
//        handler.rejectedExecution(command, this);
//    }
//
//    /**
//     * Performs any further cleanup following run state transition on
//     * invocation of shutdown.  A no-op here, but used by
//     * ScheduledThreadPoolExecutor to cancel delayed tasks.
//     */
//    void onShutdown() {
//    }
//
//    /**
//     * State check needed by ScheduledThreadPoolExecutor to
//     * enable running tasks during shutdown.
//     *
//     * @param shutdownOK true if should return true if SHUTDOWN
//     */
//    final boolean isRunningOrShutdown(boolean shutdownOK) {
//        int rs = runStateOf(ctl.get());
//        return rs == RUNNING || (rs == SHUTDOWN && shutdownOK);
//    }
//
//    /**
//     * Drains the task queue into a new list, normally using
//     * drainTo. But if the queue is a DelayQueue or any other kind of
//     * queue for which poll or drainTo may fail to remove some
//     * elements, it deletes them one by one.
//     */
//    private List<Runnable> drainQueue() {
//        BlockingQueue<Runnable> q = workQueue;
//        ArrayList<Runnable> taskList = new ArrayList<Runnable>();
//        q.drainTo(taskList);
//        if (!q.isEmpty()) {
//            for (Runnable r : q.toArray(new Runnable[0])) {
//                if (q.remove(r))
//                    taskList.add(r);
//            }
//        }
//        return taskList;
//    }
//
//    /*
//     * Methods for creating, running and cleaning up after workers
//     */
//
//    /** 新建工作线程执行任务，core标识是否是核心线程 */
//    private boolean addWorker(Runnable firstTask, boolean core) {
//        /** 循环标记点：continue retry表示从此标记点继续循环，break retry表示跳过该循环 */
//        retry:
//        /** 这段双自旋逻辑主要是对worker数量做原子+1 */
//        for (;;) {
//            int c = ctl.get();
//            int rs = runStateOf(c);
//
//            /** 1、线程池处于SHUTDOWN状态，拒绝添加新任务，返回失败
//                2、线程池处于非运行状态，且任务为空，返回失败
//                3、线程池处于非运行状态，阻塞队列已满，返回失败 */
//            if (rs >= SHUTDOWN &&
//                    ! (rs == SHUTDOWN &&
//                            firstTask == null &&
//                            ! workQueue.isEmpty()))
//                return false;
//
//            for (;;) {
//                int wc = workerCountOf(c);
//                /** 1、如果线程数量已经超过线程池容量，返回失败
//                    2、根据传入核心池标记判断，如果线程数>=核心池或者最大池，返回失败 */
//                if (wc >= CAPACITY ||
//                        wc >= (core ? corePoolSize : maximumPoolSize))
//                    return false;
//                /** cas新增一个工作线程数 */
//                if (compareAndIncrementWorkerCount(c))
//                    break retry;
//                c = ctl.get();
//                if (runStateOf(c) != rs)
//                    continue retry;
//            }
//        }
//
//        /** 工作线程是否启动标识 */
//        boolean workerStarted = false;
//
//        /** 工作线程是否添加成功标识 */
//        boolean workerAdded = false;
//        Worker w = null;
//        try {
//            /** 构建worker，继承了AQS，实现了Runnable */
//            w = new Worker(firstTask);
//            final Thread t = w.thread;
//            if (t != null) {
//                final ReentrantLock mainLock = this.mainLock;
//                /** 获取可重入的独占锁,HashSet底层是HashMap，是线程不安全的 */
//                mainLock.lock();
//                try {
//                    int rs = runStateOf(ctl.get());
//
//                    if (rs < SHUTDOWN ||
//                            (rs == SHUTDOWN && firstTask == null)) {
//                        /** 工作线程还没有启动就已经是运行状态，则抛出异常 */
//                        if (t.isAlive())
//                            throw new IllegalThreadStateException();
//                        /** 工作线程添加到HashSet集合中 */
//                        workers.add(w);
//                        int s = workers.size();
//                        if (s > largestPoolSize)
//                            largestPoolSize = s;
//                        workerAdded = true;
//                    }
//                } finally {
//                    mainLock.unlock();
//                }
//                /** worker添加成功，则启动线程 */
//                if (workerAdded) {
//                    t.start();
//                    workerStarted = true;
//                }
//            }
//        } finally {
//            /** worker启动失败，则回滚工作线程数 */
//            if (! workerStarted)
//                addWorkerFailed(w);
//        }
//        return workerStarted;
//    }
//
//    /**
//     * Rolls back the worker thread creation.
//     * - removes worker from workers, if present
//     * - decrements worker count
//     * - rechecks for termination, in case the existence of this
//     *   worker was holding up termination
//     */
//    private void addWorkerFailed(Worker w) {
//        final ReentrantLock mainLock = this.mainLock;
//        mainLock.lock();
//        try {
//            if (w != null)
//                workers.remove(w);
//            decrementWorkerCount();
//            tryTerminate();
//        } finally {
//            mainLock.unlock();
//        }
//    }
//
//    /** 工作线程退出 */
//    private void processWorkerExit(Worker w, boolean completedAbruptly) {
//        if (completedAbruptly) // If abrupt, then workerCount wasn't adjusted
//            decrementWorkerCount();
//
//        final ReentrantLock mainLock = this.mainLock;
//        mainLock.lock();
//        try {
//            completedTaskCount += w.completedTasks;
//            workers.remove(w);
//        } finally {
//            mainLock.unlock();
//        }
//
//        tryTerminate();
//
//        int c = ctl.get();
//        if (runStateLessThan(c, STOP)) {
//            if (!completedAbruptly) {
//                int min = allowCoreThreadTimeOut ? 0 : corePoolSize;
//                if (min == 0 && ! workQueue.isEmpty())
//                    min = 1;
//                if (workerCountOf(c) >= min)
//                    return; // replacement not needed
//            }
//            addWorker(null, false);
//        }
//    }
//
//    /** 从阻塞队列中获取任务 */
//    private Runnable getTask() {
//        boolean timedOut = false; // Did the last poll() time out?
//
//        for (;;) {
//            int c = ctl.get();
//            int rs = runStateOf(c);
//
//            /** 如果线程池状态>shutdown并且队列为空时，或者当前状态>stop时，当前work应该退出 */
//            if (rs >= SHUTDOWN && (rs >= STOP || workQueue.isEmpty())) {
//                decrementWorkerCount();
//                return null;
//            }
//
//            int wc = workerCountOf(c);
//
//            /** allowCoreThreadTimeOut是核心线程的超时标识，默认为false，或者线程数超过了核心线程数 */
//            boolean timed = allowCoreThreadTimeOut || wc > corePoolSize;
//
//            /** 如果超时获取任务了，则返回null，销毁线程 */
//            if ((wc > maximumPoolSize || (timed && timedOut))
//                    && (wc > 1 || workQueue.isEmpty())) {
//                if (compareAndDecrementWorkerCount(c))
//                    return null;
//                continue;
//            }
//
//            try {
//                /** 根据timed的值来觉得用等待超时方法还是阻塞方法获取任务 */
//                Runnable r = timed ?
//                        workQueue.poll(keepAliveTime, TimeUnit.NANOSECONDS) :
//                        workQueue.take();
//                if (r != null)
//                    return r;
//                /** r==null，说明超时了，下次自旋时，线程将会被销毁 */
//                timedOut = true;
//            } catch (InterruptedException retry) {
//                timedOut = false;
//            }
//        }
//    }
//
//    /** 运行工作线程 */
//    final void runWorker(Worker w) {
//        Thread wt = Thread.currentThread();
//        Runnable task = w.firstTask;
//        w.firstTask = null;
//        /** unlock后，更新state为0，表示可以响应中断了，因为new worker默认state=-1，中断要state>=0才允许调用 */
//        w.unlock();
//        boolean completedAbruptly = true;
//        try {
//            /** 如果任务为空，则从阻塞队列中获取任务，无限循环，除非被销毁 */
//            while (task != null || (task = getTask()) != null) {
//                /** 上锁是为了在shutdown()时不终止正在运行的worker */
//                w.lock();
//                if ((runStateAtLeast(ctl.get(), STOP) ||
//                        (Thread.interrupted() &&
//                                runStateAtLeast(ctl.get(), STOP))) &&
//                        !wt.isInterrupted())
//                    wt.interrupt();
//                try {
//                    /** 预留钩子方法，可以继承重写 */
//                    beforeExecute(wt, task);
//                    Throwable thrown = null;
//                    try {
//                        task.run();
//                    } catch (RuntimeException x) {
//                        thrown = x; throw x;
//                    } catch (Error x) {
//                        thrown = x; throw x;
//                    } catch (Throwable x) {
//                        thrown = x; throw new Error(x);
//                    } finally {
//                        /** 预留钩子方法，可以继承重写 */
//                        afterExecute(task, thrown);
//                    }
//                } finally {
//                    task = null;
//                    w.completedTasks++;
//                    w.unlock();
//                }
//            }
//            completedAbruptly = false;
//        } finally {
//            /** 将worker从集合workers里删除掉 */
//            processWorkerExit(w, completedAbruptly);
//        }
//    }
//
//    // Public constructors and methods
//
//    /**
//     * Creates a new {@code ThreadPoolExecutor} with the given initial
//     * parameters and default thread factory and rejected execution handler.
//     * It may be more convenient to use one of the {@link Executors} factory
//     * methods instead of this general purpose constructor.
//     *
//     * @param corePoolSize the number of threads to keep in the pool, even
//     *        if they are idle, unless {@code allowCoreThreadTimeOut} is set
//     * @param maximumPoolSize the maximum number of threads to allow in the
//     *        pool
//     * @param keepAliveTime when the number of threads is greater than
//     *        the core, this is the maximum time that excess idle threads
//     *        will wait for new tasks before terminating.
//     * @param unit the time unit for the {@code keepAliveTime} argument
//     * @param workQueue the queue to use for holding tasks before they are
//     *        executed.  This queue will hold only the {@code Runnable}
//     *        tasks submitted by the {@code execute} method.
//     * @throws IllegalArgumentException if one of the following holds:<br>
//     *         {@code corePoolSize < 0}<br>
//     *         {@code keepAliveTime < 0}<br>
//     *         {@code maximumPoolSize <= 0}<br>
//     *         {@code maximumPoolSize < corePoolSize}
//     * @throws NullPointerException if {@code workQueue} is null
//     */
//    public ThreadPoolExecutor(int corePoolSize,
//                              int maximumPoolSize,
//                              long keepAliveTime,
//                              TimeUnit unit,
//                              BlockingQueue<Runnable> workQueue) {
//        this(corePoolSize, maximumPoolSize, keepAliveTime, unit, workQueue,
//                Executors.defaultThreadFactory(), defaultHandler);
//    }
//
//    /**
//     * Creates a new {@code ThreadPoolExecutor} with the given initial
//     * parameters and default rejected execution handler.
//     *
//     * @param corePoolSize the number of threads to keep in the pool, even
//     *        if they are idle, unless {@code allowCoreThreadTimeOut} is set
//     * @param maximumPoolSize the maximum number of threads to allow in the
//     *        pool
//     * @param keepAliveTime when the number of threads is greater than
//     *        the core, this is the maximum time that excess idle threads
//     *        will wait for new tasks before terminating.
//     * @param unit the time unit for the {@code keepAliveTime} argument
//     * @param workQueue the queue to use for holding tasks before they are
//     *        executed.  This queue will hold only the {@code Runnable}
//     *        tasks submitted by the {@code execute} method.
//     * @param threadFactory the factory to use when the executor
//     *        creates a new thread
//     * @throws IllegalArgumentException if one of the following holds:<br>
//     *         {@code corePoolSize < 0}<br>
//     *         {@code keepAliveTime < 0}<br>
//     *         {@code maximumPoolSize <= 0}<br>
//     *         {@code maximumPoolSize < corePoolSize}
//     * @throws NullPointerException if {@code workQueue}
//     *         or {@code threadFactory} is null
//     */
//    public ThreadPoolExecutor(int corePoolSize,
//                              int maximumPoolSize,
//                              long keepAliveTime,
//                              TimeUnit unit,
//                              BlockingQueue<Runnable> workQueue,
//                              ThreadFactory threadFactory) {
//        this(corePoolSize, maximumPoolSize, keepAliveTime, unit, workQueue,
//                threadFactory, defaultHandler);
//    }
//
//    /**
//     * Creates a new {@code ThreadPoolExecutor} with the given initial
//     * parameters and default thread factory.
//     *
//     * @param corePoolSize the number of threads to keep in the pool, even
//     *        if they are idle, unless {@code allowCoreThreadTimeOut} is set
//     * @param maximumPoolSize the maximum number of threads to allow in the
//     *        pool
//     * @param keepAliveTime when the number of threads is greater than
//     *        the core, this is the maximum time that excess idle threads
//     *        will wait for new tasks before terminating.
//     * @param unit the time unit for the {@code keepAliveTime} argument
//     * @param workQueue the queue to use for holding tasks before they are
//     *        executed.  This queue will hold only the {@code Runnable}
//     *        tasks submitted by the {@code execute} method.
//     * @param handler the handler to use when execution is blocked
//     *        because the thread bounds and queue capacities are reached
//     * @throws IllegalArgumentException if one of the following holds:<br>
//     *         {@code corePoolSize < 0}<br>
//     *         {@code keepAliveTime < 0}<br>
//     *         {@code maximumPoolSize <= 0}<br>
//     *         {@code maximumPoolSize < corePoolSize}
//     * @throws NullPointerException if {@code workQueue}
//     *         or {@code handler} is null
//     */
//    public ThreadPoolExecutor(int corePoolSize,
//                              int maximumPoolSize,
//                              long keepAliveTime,
//                              TimeUnit unit,
//                              BlockingQueue<Runnable> workQueue,
//                              RejectedExecutionHandler handler) {
//        this(corePoolSize, maximumPoolSize, keepAliveTime, unit, workQueue,
//                Executors.defaultThreadFactory(), handler);
//    }
//
//    /**
//     * Creates a new {@code ThreadPoolExecutor} with the given initial
//     * parameters.
//     *
//     * @param corePoolSize the number of threads to keep in the pool, even
//     *        if they are idle, unless {@code allowCoreThreadTimeOut} is set
//     * @param maximumPoolSize the maximum number of threads to allow in the
//     *        pool
//     * @param keepAliveTime when the number of threads is greater than
//     *        the core, this is the maximum time that excess idle threads
//     *        will wait for new tasks before terminating.
//     * @param unit the time unit for the {@code keepAliveTime} argument
//     * @param workQueue the queue to use for holding tasks before they are
//     *        executed.  This queue will hold only the {@code Runnable}
//     *        tasks submitted by the {@code execute} method.
//     * @param threadFactory the factory to use when the executor
//     *        creates a new thread
//     * @param handler the handler to use when execution is blocked
//     *        because the thread bounds and queue capacities are reached
//     * @throws IllegalArgumentException if one of the following holds:<br>
//     *         {@code corePoolSize < 0}<br>
//     *         {@code keepAliveTime < 0}<br>
//     *         {@code maximumPoolSize <= 0}<br>
//     *         {@code maximumPoolSize < corePoolSize}
//     * @throws NullPointerException if {@code workQueue}
//     *         or {@code threadFactory} or {@code handler} is null
//     */
//    public ThreadPoolExecutor(int corePoolSize,
//                              int maximumPoolSize,
//                              long keepAliveTime,
//                              TimeUnit unit,
//                              BlockingQueue<Runnable> workQueue,
//                              ThreadFactory threadFactory,
//                              RejectedExecutionHandler handler) {
//        if (corePoolSize < 0 ||
//                maximumPoolSize <= 0 ||
//                maximumPoolSize < corePoolSize ||
//                keepAliveTime < 0)
//            throw new IllegalArgumentException();
//        if (workQueue == null || threadFactory == null || handler == null)
//            throw new NullPointerException();
//        this.acc = System.getSecurityManager() == null ?
//                null :
//                AccessController.getContext();
//        this.corePoolSize = corePoolSize;
//        this.maximumPoolSize = maximumPoolSize;
//        this.workQueue = workQueue;
//        this.keepAliveTime = unit.toNanos(keepAliveTime);
//        this.threadFactory = threadFactory;
//        this.handler = handler;
//    }
//
//    /** 执行一个新任务 */
//    public void execute(Runnable command) {
//        if (command == null)
//            throw new NullPointerException();
//
//        /** 获取当前线程池状态+线程数量 */
//        int c = ctl.get();
//        /** 如果线程数<核心线程数，则创建一个工作线程去处理该任务 */
//        if (workerCountOf(c) < corePoolSize) {
//            if (addWorker(command, true))
//                return;
//            c = ctl.get();
//        }
//        /** 如果线程池状态是运行中，则添加任务到阻塞队列 */
//        if (isRunning(c) && workQueue.offer(command)) {
//            int recheck = ctl.get();
//            /** 如果线程池状态是不是运行中，则把该任务从阻塞队列中移除，并根据拒绝策略处理任务 */
//            if (! isRunning(recheck) && remove(command))
//                reject(command);
//            else if (workerCountOf(recheck) == 0)
//                addWorker(null, false);
//        }
//        /** 如果核心线程数已满，队列已满，则试着创建一个新线程（如果最大线程数>核心线程数） */
//        else if (!addWorker(command, false))
//            reject(command);
//    }
//
//    /** 线程池关闭 */
//    public void shutdown() {
//        final ReentrantLock mainLock = this.mainLock;
//        mainLock.lock();
//        try {
//            checkShutdownAccess();
//            advanceRunState(SHUTDOWN);
//            interruptIdleWorkers();
//            onShutdown(); // hook for ScheduledThreadPoolExecutor
//        } finally {
//            mainLock.unlock();
//        }
//        tryTerminate();
//    }
//
//    /**
//     * Attempts to stop all actively executing tasks, halts the
//     * processing of waiting tasks, and returns a list of the tasks
//     * that were awaiting execution. These tasks are drained (removed)
//     * from the task queue upon return from this method.
//     *
//     * <p>This method does not wait for actively executing tasks to
//     * terminate.  Use {@link #awaitTermination awaitTermination} to
//     * do that.
//     *
//     * <p>There are no guarantees beyond best-effort attempts to stop
//     * processing actively executing tasks.  This implementation
//     * cancels tasks via {@link Thread#interrupt}, so any task that
//     * fails to respond to interrupts may never terminate.
//     *
//     * @throws SecurityException {@inheritDoc}
//     */
//    public List<Runnable> shutdownNow() {
//        List<Runnable> tasks;
//        final ReentrantLock mainLock = this.mainLock;
//        mainLock.lock();
//        try {
//            checkShutdownAccess();
//            advanceRunState(STOP);
//            interruptWorkers();
//            tasks = drainQueue();
//        } finally {
//            mainLock.unlock();
//        }
//        tryTerminate();
//        return tasks;
//    }
//
//    public boolean isShutdown() {
//        return ! isRunning(ctl.get());
//    }
//
//    /**
//     * Returns true if this executor is in the process of terminating
//     * after {@link #shutdown} or {@link #shutdownNow} but has not
//     * completely terminated.  This method may be useful for
//     * debugging. A return of {@code true} reported a sufficient
//     * period after shutdown may indicate that submitted tasks have
//     * ignored or suppressed interruption, causing this executor not
//     * to properly terminate.
//     *
//     * @return {@code true} if terminating but not yet terminated
//     */
//    public boolean isTerminating() {
//        int c = ctl.get();
//        return ! isRunning(c) && runStateLessThan(c, TERMINATED);
//    }
//
//    public boolean isTerminated() {
//        return runStateAtLeast(ctl.get(), TERMINATED);
//    }
//
//    public boolean awaitTermination(long timeout, TimeUnit unit)
//            throws InterruptedException {
//        long nanos = unit.toNanos(timeout);
//        final ReentrantLock mainLock = this.mainLock;
//        mainLock.lock();
//        try {
//            for (;;) {
//                if (runStateAtLeast(ctl.get(), TERMINATED))
//                    return true;
//                if (nanos <= 0)
//                    return false;
//                nanos = termination.awaitNanos(nanos);
//            }
//        } finally {
//            mainLock.unlock();
//        }
//    }
//
//    /**
//     * Invokes {@code shutdown} when this executor is no longer
//     * referenced and it has no threads.
//     */
//    protected void finalize() {
//        SecurityManager sm = System.getSecurityManager();
//        if (sm == null || acc == null) {
//            shutdown();
//        } else {
//            PrivilegedAction<Void> pa = () -> { shutdown(); return null; };
//            AccessController.doPrivileged(pa, acc);
//        }
//    }
//
//    /**
//     * Sets the thread factory used to create new threads.
//     *
//     * @param threadFactory the new thread factory
//     * @throws NullPointerException if threadFactory is null
//     * @see #getThreadFactory
//     */
//    public void setThreadFactory(ThreadFactory threadFactory) {
//        if (threadFactory == null)
//            throw new NullPointerException();
//        this.threadFactory = threadFactory;
//    }
//
//    /**
//     * Returns the thread factory used to create new threads.
//     *
//     * @return the current thread factory
//     * @see #setThreadFactory(ThreadFactory)
//     */
//    public ThreadFactory getThreadFactory() {
//        return threadFactory;
//    }
//
//    /**
//     * Sets a new handler for unexecutable tasks.
//     *
//     * @param handler the new handler
//     * @throws NullPointerException if handler is null
//     * @see #getRejectedExecutionHandler
//     */
//    public void setRejectedExecutionHandler(RejectedExecutionHandler handler) {
//        if (handler == null)
//            throw new NullPointerException();
//        this.handler = handler;
//    }
//
//    /**
//     * Returns the current handler for unexecutable tasks.
//     *
//     * @return the current handler
//     * @see #setRejectedExecutionHandler(RejectedExecutionHandler)
//     */
//    public RejectedExecutionHandler getRejectedExecutionHandler() {
//        return handler;
//    }
//
//    /**
//     * Sets the core number of threads.  This overrides any value set
//     * in the constructor.  If the new value is smaller than the
//     * current value, excess existing threads will be terminated when
//     * they next become idle.  If larger, new threads will, if needed,
//     * be started to execute any queued tasks.
//     *
//     * @param corePoolSize the new core size
//     * @throws IllegalArgumentException if {@code corePoolSize < 0}
//     * @see #getCorePoolSize
//     */
//    public void setCorePoolSize(int corePoolSize) {
//        if (corePoolSize < 0)
//            throw new IllegalArgumentException();
//        int delta = corePoolSize - this.corePoolSize;
//        this.corePoolSize = corePoolSize;
//        if (workerCountOf(ctl.get()) > corePoolSize)
//            interruptIdleWorkers();
//        else if (delta > 0) {
//            // We don't really know how many new threads are "needed".
//            // As a heuristic, prestart enough new workers (up to new
//            // core size) to handle the current number of tasks in
//            // queue, but stop if queue becomes empty while doing so.
//            int k = Math.min(delta, workQueue.size());
//            while (k-- > 0 && addWorker(null, true)) {
//                if (workQueue.isEmpty())
//                    break;
//            }
//        }
//    }
//
//    /**
//     * Returns the core number of threads.
//     *
//     * @return the core number of threads
//     * @see #setCorePoolSize
//     */
//    public int getCorePoolSize() {
//        return corePoolSize;
//    }
//
//    /**
//     * Starts a core thread, causing it to idly wait for work. This
//     * overrides the default policy of starting core threads only when
//     * new tasks are executed. This method will return {@code false}
//     * if all core threads have already been started.
//     *
//     * @return {@code true} if a thread was started
//     */
//    public boolean prestartCoreThread() {
//        return workerCountOf(ctl.get()) < corePoolSize &&
//                addWorker(null, true);
//    }
//
//    /**
//     * Same as prestartCoreThread except arranges that at least one
//     * thread is started even if corePoolSize is 0.
//     */
//    void ensurePrestart() {
//        int wc = workerCountOf(ctl.get());
//        if (wc < corePoolSize)
//            addWorker(null, true);
//        else if (wc == 0)
//            addWorker(null, false);
//    }
//
//    /**
//     * Starts all core threads, causing them to idly wait for work. This
//     * overrides the default policy of starting core threads only when
//     * new tasks are executed.
//     *
//     * @return the number of threads started
//     */
//    public int prestartAllCoreThreads() {
//        int n = 0;
//        while (addWorker(null, true))
//            ++n;
//        return n;
//    }
//
//    /**
//     * Returns true if this pool allows core threads to time out and
//     * terminate if no tasks arrive within the keepAlive time, being
//     * replaced if needed when new tasks arrive. When true, the same
//     * keep-alive policy applying to non-core threads applies also to
//     * core threads. When false (the default), core threads are never
//     * terminated due to lack of incoming tasks.
//     *
//     * @return {@code true} if core threads are allowed to time out,
//     *         else {@code false}
//     *
//     * @since 1.6
//     */
//    public boolean allowsCoreThreadTimeOut() {
//        return allowCoreThreadTimeOut;
//    }
//
//    /**
//     * Sets the policy governing whether core threads may time out and
//     * terminate if no tasks arrive within the keep-alive time, being
//     * replaced if needed when new tasks arrive. When false, core
//     * threads are never terminated due to lack of incoming
//     * tasks. When true, the same keep-alive policy applying to
//     * non-core threads applies also to core threads. To avoid
//     * continual thread replacement, the keep-alive time must be
//     * greater than zero when setting {@code true}. This method
//     * should in general be called before the pool is actively used.
//     *
//     * @param value {@code true} if should time out, else {@code false}
//     * @throws IllegalArgumentException if value is {@code true}
//     *         and the current keep-alive time is not greater than zero
//     *
//     * @since 1.6
//     */
//    public void allowCoreThreadTimeOut(boolean value) {
//        if (value && keepAliveTime <= 0)
//            throw new IllegalArgumentException("Core threads must have nonzero keep alive times");
//        if (value != allowCoreThreadTimeOut) {
//            allowCoreThreadTimeOut = value;
//            if (value)
//                interruptIdleWorkers();
//        }
//    }
//
//    /**
//     * Sets the maximum allowed number of threads. This overrides any
//     * value set in the constructor. If the new value is smaller than
//     * the current value, excess existing threads will be
//     * terminated when they next become idle.
//     *
//     * @param maximumPoolSize the new maximum
//     * @throws IllegalArgumentException if the new maximum is
//     *         less than or equal to zero, or
//     *         less than the {@linkplain #getCorePoolSize core pool size}
//     * @see #getMaximumPoolSize
//     */
//    public void setMaximumPoolSize(int maximumPoolSize) {
//        if (maximumPoolSize <= 0 || maximumPoolSize < corePoolSize)
//            throw new IllegalArgumentException();
//        this.maximumPoolSize = maximumPoolSize;
//        if (workerCountOf(ctl.get()) > maximumPoolSize)
//            interruptIdleWorkers();
//    }
//
//    /**
//     * Returns the maximum allowed number of threads.
//     *
//     * @return the maximum allowed number of threads
//     * @see #setMaximumPoolSize
//     */
//    public int getMaximumPoolSize() {
//        return maximumPoolSize;
//    }
//
//    /**
//     * Sets the time limit for which threads may remain idle before
//     * being terminated.  If there are more than the core number of
//     * threads currently in the pool, after waiting this amount of
//     * time without processing a task, excess threads will be
//     * terminated.  This overrides any value set in the constructor.
//     *
//     * @param time the time to wait.  A time value of zero will cause
//     *        excess threads to terminate immediately after executing tasks.
//     * @param unit the time unit of the {@code time} argument
//     * @throws IllegalArgumentException if {@code time} less than zero or
//     *         if {@code time} is zero and {@code allowsCoreThreadTimeOut}
//     * @see #getKeepAliveTime(TimeUnit)
//     */
//    public void setKeepAliveTime(long time, TimeUnit unit) {
//        if (time < 0)
//            throw new IllegalArgumentException();
//        if (time == 0 && allowsCoreThreadTimeOut())
//            throw new IllegalArgumentException("Core threads must have nonzero keep alive times");
//        long keepAliveTime = unit.toNanos(time);
//        long delta = keepAliveTime - this.keepAliveTime;
//        this.keepAliveTime = keepAliveTime;
//        if (delta < 0)
//            interruptIdleWorkers();
//    }
//
//    /**
//     * Returns the thread keep-alive time, which is the amount of time
//     * that threads in excess of the core pool size may remain
//     * idle before being terminated.
//     *
//     * @param unit the desired time unit of the result
//     * @return the time limit
//     * @see #setKeepAliveTime(long, TimeUnit)
//     */
//    public long getKeepAliveTime(TimeUnit unit) {
//        return unit.convert(keepAliveTime, TimeUnit.NANOSECONDS);
//    }
//
//    /* User-level queue utilities */
//
//    /**
//     * Returns the task queue used by this executor. Access to the
//     * task queue is intended primarily for debugging and monitoring.
//     * This queue may be in active use.  Retrieving the task queue
//     * does not prevent queued tasks from executing.
//     *
//     * @return the task queue
//     */
//    public BlockingQueue<Runnable> getQueue() {
//        return workQueue;
//    }
//
//    /**
//     * Removes this task from the executor's internal queue if it is
//     * present, thus causing it not to be run if it has not already
//     * started.
//     *
//     * <p>This method may be useful as one part of a cancellation
//     * scheme.  It may fail to remove tasks that have been converted
//     * into other forms before being placed on the internal queue. For
//     * example, a task entered using {@code submit} might be
//     * converted into a form that maintains {@code Future} status.
//     * However, in such cases, method {@link #purge} may be used to
//     * remove those Futures that have been cancelled.
//     *
//     * @param task the task to remove
//     * @return {@code true} if the task was removed
//     */
//    public boolean remove(Runnable task) {
//        boolean removed = workQueue.remove(task);
//        tryTerminate(); // In case SHUTDOWN and now empty
//        return removed;
//    }
//
//    /**
//     * Tries to remove from the work queue all {@link Future}
//     * tasks that have been cancelled. This method can be useful as a
//     * storage reclamation operation, that has no other impact on
//     * functionality. Cancelled tasks are never executed, but may
//     * accumulate in work queues until worker threads can actively
//     * remove them. Invoking this method instead tries to remove them now.
//     * However, this method may fail to remove tasks in
//     * the presence of interference by other threads.
//     */
//    public void purge() {
//        final BlockingQueue<Runnable> q = workQueue;
//        try {
//            Iterator<Runnable> it = q.iterator();
//            while (it.hasNext()) {
//                Runnable r = it.next();
//                if (r instanceof Future<?> && ((Future<?>)r).isCancelled())
//                    it.remove();
//            }
//        } catch (ConcurrentModificationException fallThrough) {
//            // Take slow path if we encounter interference during traversal.
//            // Make copy for traversal and call remove for cancelled entries.
//            // The slow path is more likely to be O(N*N).
//            for (Object r : q.toArray())
//                if (r instanceof Future<?> && ((Future<?>)r).isCancelled())
//                    q.remove(r);
//        }
//
//        tryTerminate(); // In case SHUTDOWN and now empty
//    }
//
//    /* Statistics */
//
//    /**
//     * Returns the current number of threads in the pool.
//     *
//     * @return the number of threads
//     */
//    public int getPoolSize() {
//        final ReentrantLock mainLock = this.mainLock;
//        mainLock.lock();
//        try {
//            // Remove rare and surprising possibility of
//            // isTerminated() && getPoolSize() > 0
//            return runStateAtLeast(ctl.get(), TIDYING) ? 0
//                    : workers.size();
//        } finally {
//            mainLock.unlock();
//        }
//    }
//
//    /**
//     * Returns the approximate number of threads that are actively
//     * executing tasks.
//     *
//     * @return the number of threads
//     */
//    public int getActiveCount() {
//        final ReentrantLock mainLock = this.mainLock;
//        mainLock.lock();
//        try {
//            int n = 0;
//            for (Worker w : workers)
//                if (w.isLocked())
//                    ++n;
//            return n;
//        } finally {
//            mainLock.unlock();
//        }
//    }
//
//    /**
//     * Returns the largest number of threads that have ever
//     * simultaneously been in the pool.
//     *
//     * @return the number of threads
//     */
//    public int getLargestPoolSize() {
//        final ReentrantLock mainLock = this.mainLock;
//        mainLock.lock();
//        try {
//            return largestPoolSize;
//        } finally {
//            mainLock.unlock();
//        }
//    }
//
//    /**
//     * Returns the approximate total number of tasks that have ever been
//     * scheduled for execution. Because the states of tasks and
//     * threads may change dynamically during computation, the returned
//     * value is only an approximation.
//     *
//     * @return the number of tasks
//     */
//    public long getTaskCount() {
//        final ReentrantLock mainLock = this.mainLock;
//        mainLock.lock();
//        try {
//            long n = completedTaskCount;
//            for (Worker w : workers) {
//                n += w.completedTasks;
//                if (w.isLocked())
//                    ++n;
//            }
//            return n + workQueue.size();
//        } finally {
//            mainLock.unlock();
//        }
//    }
//
//    /**
//     * Returns the approximate total number of tasks that have
//     * completed execution. Because the states of tasks and threads
//     * may change dynamically during computation, the returned value
//     * is only an approximation, but one that does not ever decrease
//     * across successive calls.
//     *
//     * @return the number of tasks
//     */
//    public long getCompletedTaskCount() {
//        final ReentrantLock mainLock = this.mainLock;
//        mainLock.lock();
//        try {
//            long n = completedTaskCount;
//            for (Worker w : workers)
//                n += w.completedTasks;
//            return n;
//        } finally {
//            mainLock.unlock();
//        }
//    }
//
//    /**
//     * Returns a string identifying this pool, as well as its state,
//     * including indications of run state and estimated worker and
//     * task counts.
//     *
//     * @return a string identifying this pool, as well as its state
//     */
//    public String toString() {
//        long ncompleted;
//        int nworkers, nactive;
//        final ReentrantLock mainLock = this.mainLock;
//        mainLock.lock();
//        try {
//            ncompleted = completedTaskCount;
//            nactive = 0;
//            nworkers = workers.size();
//            for (Worker w : workers) {
//                ncompleted += w.completedTasks;
//                if (w.isLocked())
//                    ++nactive;
//            }
//        } finally {
//            mainLock.unlock();
//        }
//        int c = ctl.get();
//        String rs = (runStateLessThan(c, SHUTDOWN) ? "Running" :
//                (runStateAtLeast(c, TERMINATED) ? "Terminated" :
//                        "Shutting down"));
//        return super.toString() +
//                "[" + rs +
//                ", pool size = " + nworkers +
//                ", active threads = " + nactive +
//                ", queued tasks = " + workQueue.size() +
//                ", completed tasks = " + ncompleted +
//                "]";
//    }
//
//    /* Extension hooks */
//
//    /**
//     * Method invoked prior to executing the given Runnable in the
//     * given thread.  This method is invoked by thread {@code t} that
//     * will execute task {@code r}, and may be used to re-initialize
//     * ThreadLocals, or to perform logging.
//     *
//     * <p>This implementation does nothing, but may be customized in
//     * subclasses. Note: To properly nest multiple overridings, subclasses
//     * should generally invoke {@code super.beforeExecute} at the end of
//     * this method.
//     *
//     * @param t the thread that will run task {@code r}
//     * @param r the task that will be executed
//     */
//    protected void beforeExecute(Thread t, Runnable r) { }
//
//    /**
//     * Method invoked upon completion of execution of the given Runnable.
//     * This method is invoked by the thread that executed the task. If
//     * non-null, the Throwable is the uncaught {@code RuntimeException}
//     * or {@code Error} that caused execution to terminate abruptly.
//     *
//     * <p>This implementation does nothing, but may be customized in
//     * subclasses. Note: To properly nest multiple overridings, subclasses
//     * should generally invoke {@code super.afterExecute} at the
//     * beginning of this method.
//     *
//     * <p><b>Note:</b> When actions are enclosed in tasks (such as
//     * {@link FutureTask}) either explicitly or via methods such as
//     * {@code submit}, these task objects catch and maintain
//     * computational exceptions, and so they do not cause abrupt
//     * termination, and the internal exceptions are <em>not</em>
//     * passed to this method. If you would like to trap both kinds of
//     * failures in this method, you can further probe for such cases,
//     * as in this sample subclass that prints either the direct cause
//     * or the underlying exception if a task has been aborted:
//     *
//     *  <pre> {@code
//     * class ExtendedExecutor extends ThreadPoolExecutor {
//     *   // ...
//     *   protected void afterExecute(Runnable r, Throwable t) {
//     *     super.afterExecute(r, t);
//     *     if (t == null && r instanceof Future<?>) {
//     *       try {
//     *         Object result = ((Future<?>) r).get();
//     *       } catch (CancellationException ce) {
//     *           t = ce;
//     *       } catch (ExecutionException ee) {
//     *           t = ee.getCause();
//     *       } catch (InterruptedException ie) {
//     *           Thread.currentThread().interrupt(); // ignore/reset
//     *       }
//     *     }
//     *     if (t != null)
//     *       System.out.println(t);
//     *   }
//     * }}</pre>
//     *
//     * @param r the runnable that has completed
//     * @param t the exception that caused termination, or null if
//     * execution completed normally
//     */
//    protected void afterExecute(Runnable r, Throwable t) { }
//
//    /**
//     * Method invoked when the Executor has terminated.  Default
//     * implementation does nothing. Note: To properly nest multiple
//     * overridings, subclasses should generally invoke
//     * {@code super.terminated} within this method.
//     */
//    protected void terminated() { }
//
//    /* Predefined RejectedExecutionHandlers */
//
//    /** 拒绝策略：让提交任务的线程执行该任务 */
//    public static class CallerRunsPolicy implements RejectedExecutionHandler {
//
//        public CallerRunsPolicy() { }
//
//        public void rejectedExecution(Runnable r, ThreadPoolExecutor e) {
//            /** 如果线程池没有关闭 */
//            if (!e.isShutdown()) {
//                r.run();
//            }
//        }
//    }
//
//    /** 默认的拒绝策略：直接抛出异常 */
//    public static class AbortPolicy implements RejectedExecutionHandler {
//
//        public AbortPolicy() { }
//
//        public void rejectedExecution(Runnable r, ThreadPoolExecutor e) {
//            throw new RejectedExecutionException("Task " + r.toString() +
//                    " rejected from " +
//                    e.toString());
//        }
//    }
//
//    /** 拒绝策略：直接丢弃任务 */
//    public static class DiscardPolicy implements RejectedExecutionHandler {
//
//        public DiscardPolicy() { }
//
//        public void rejectedExecution(Runnable r, ThreadPoolExecutor e) {
//        }
//    }
//
//    /** 拒绝策略：扔掉阻塞队列中最老的任务，然后执行当前任务 */
//    public static class DiscardOldestPolicy implements RejectedExecutionHandler {
//
//        public DiscardOldestPolicy() { }
//
//        public void rejectedExecution(Runnable r, ThreadPoolExecutor e) {
//            /** 如果线程池没有关闭 */
//            if (!e.isShutdown()) {
//                e.getQueue().poll();
//                e.execute(r);
//            }
//        }
//    }
//
//    /** 核心线程数等于最大线程数，阻塞队列大小为 Integer.MAX_VALUE */
//    public static ExecutorService newFixedThreadPool(int nThreads) {
//        return new ThreadPoolExecutor(nThreads, nThreads,
//                0L, TimeUnit.MILLISECONDS,
//                new LinkedBlockingQueue<Runnable>());
//    }
//
//    /** 只有一个线程的线程池，阻塞队列大小为 Integer.MAX_VALUE */
//    public static ExecutorService newSingleThreadExecutor() {
//        return new FinalizableDelegatedExecutorService
//                (new ThreadPoolExecutor(1, 1,
//                        0L, TimeUnit.MILLISECONDS,
//                        new LinkedBlockingQueue<Runnable>()));
//    }
//
//    /** 线程数可以弹性变化的线程池，每个线程最多空闲60秒，阻塞队列不存储任务，一直阻塞到任务被获取 */
//    public static ExecutorService newCachedThreadPool() {
//        return new ThreadPoolExecutor(0, Integer.MAX_VALUE,
//                60L, TimeUnit.SECONDS,
//                new SynchronousQueue<Runnable>());
//    }
//
//    /** 支持定时操作的线程池 */
//    public static ScheduledExecutorService newScheduledThreadPool(int corePoolSize) {
//        return new ScheduledThreadPoolExecutor(corePoolSize);
//    }
//
//}
