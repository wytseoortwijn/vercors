package vct.main;

import static org.junit.Assert.*;
import hre.io.Message;
import hre.io.MessageProcess;
import hre.util.TestReport.Verdict;

import java.io.File;
import java.net.URL;
import java.security.Permission;
import java.util.concurrent.Semaphore;

import junit.framework.TestCase;

import org.junit.Test;
import org.junit.runner.RunWith;

import sun.applet.Main;
import vct.util.Configuration;

import com.google.code.tempusfugit.concurrency.ConcurrentTestRunner;

@RunWith(ConcurrentTestRunner.class)
public class CARPTestChalice extends ToolTest {

  @Test
  public void testZeroArrayC() {
    sem_get();
    try {
      VCTResult res = run("vct", "--chalice", "//examples/carp/zero-array-ic.c");
      if (res.verdict != Verdict.Pass)
        fail("bad result : " + res.verdict);
    } finally {
      sem.release();
    }
  }

  @Test
  public void testZeroArrayJava() {
    sem_get();
    try {
      VCTResult res = run("vct", "--chalice",
          "//examples/carp/ZeroArrayIC.java");
      if (res.verdict != Verdict.Pass)
        fail("bad result : " + res.verdict);
    } finally {
      sem.release();
    }
  }

  @Test
  public void test_zero() {
    sem_get();
    try {
      VCTResult res = run("vct", "--chalice", "//examples/kernels/zero.pvl");
      res.checkVerdict(Verdict.Pass);
    } finally {
      sem.release();
    }
  }

  @Test
  public void test_zero_err() {
    sem_get();
    try {
      VCTResult res = run("vct", "--chalice", "//examples/kernels/zero-e1.pvl");
      res.checkVerdict(Verdict.Fail);
    } finally {
      sem.release();
    }
  }

  @Test
  public void test_scp_example() {
    sem_get();
    try {
      VCTResult res = run("vct", "--chalice", "--single-group",
          "//examples/kernels/scp-example.pvl");
      res.checkVerdict(Verdict.Pass);
    } finally {
      sem.release();
    }
  }

  @Test
  public void test_scp_example_err() {
    sem_get();
    try {
      VCTResult res = run("vct", "--chalice", "--single-group",
          "//examples/kernels/scp-example-e1.pvl");
      res.checkVerdict(Verdict.Fail);
      res.checkVerdict(Verdict.Fail);
    } finally {
      sem.release();
    }
  }

  @Test
  public void test_max_naive() {
    sem_get();
    try {
      VCTResult res = run("vct", "--chalice", "--single-group",
          "//examples/carp_demo/max-naive.pvl");
      res.checkVerdict(Verdict.Pass);
    } finally {
      sem.release();
    }
  }

  @Test
  public void test_max_naive_err1() {
    sem_get();
    try {
      VCTResult res = run("vct", "--chalice", "--single-group",
          "//examples/carp_demo/max-naive-e1.pvl");
      res.checkVerdict(Verdict.Fail);
    } finally {
      sem.release();
    }
  }

  @Test
  public void test_max_naive_err2() {
    sem_get();
    try {
      VCTResult res = run("vct", "--chalice", "--single-group",
          "//examples/carp_demo/max-naive-e2.pvl");
      res.checkVerdict(Verdict.Fail);
    } finally {
      sem.release();
    }
  }

  @Test
  public void test_max_two() {
    sem_get();
    try {
      VCTResult res = run("vct", "--chalice", "--single-group",
          "//examples/carp_demo/max-two.pvl");
      res.checkVerdict(Verdict.Pass);
    } finally {
      sem.release();
    }
  }

  @Test
  public void test_max_two_err() {
    sem_get();
    try {
      VCTResult res = run("vct", "--chalice", "--single-group",
          "//examples/carp_demo/max-two-e1.pvl");
      res.checkVerdict(Verdict.Fail);
    } finally {
      sem.release();
    }
  }

  @Test
  public void test_max_barrier() {
    sem_get();
    try {
      VCTResult res = run("vct", "--chalice", "--single-group",
          "--disable-post-check", "//examples/carp_demo/max-barrier.pvl");
      res.checkVerdict(Verdict.Pass);
    } finally {
      sem.release();
    }
  }

  @Test
  public void test_max_barrier_err() {
    sem_get();
    try {
      VCTResult res = run("vct", "--chalice", "--single-group",
          "--disable-post-check", "//examples/carp_demo/max-barrier-e1.pvl");
      res.checkVerdict(Verdict.Fail);
    } finally {
      sem.release();
    }
  }

}
