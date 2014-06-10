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
public class ManualTest extends ToolTest {

  @Test
  public void test_example1() {
    sem_get();
    try {
      VCTResult res = run("vct", "--chalice", "--no-context",
          "//examples/manual/main.pvl", "//examples/manual/permissions.pvl");
      res.mustSay("Assertion might not hold.");

      if (res.verdict != Verdict.Fail)
        fail("bad result : " + res.verdict);
    } finally {
      sem.release();
    }
  }

  @Test
  public void test_example2() {
    sem_get();
    try {
      VCTResult res = run("vct", "--chalice", "--no-context",
          "//examples/manual/loop.pvl", "//examples/manual/permissions.pvl");
      if (res.verdict != Verdict.Pass)
        fail("bad result : " + res.verdict);
    } finally {
      sem.release();
    }
  }

  @Test
  public void test_example3() {
    sem_get();
    try {
      VCTResult res = run("vct", "--chalice",
          "//examples/manual/parameters1.pvl",
          "//examples/manual/permissions.pvl");
      res.mustSay("Location might not be writable");
      if (res.verdict != Verdict.Fail)
        fail("bad result : " + res.verdict);
    } finally {
      sem.release();
    }
  }

  @Test
  public void test_example4() {
    sem_get();
    try {
      VCTResult res = run("vct", "--chalice",
          "//examples/manual/parameters2.pvl",
          "//examples/manual/permissions.pvl");
      if (res.verdict != Verdict.Pass)
        fail("bad result : " + res.verdict);
    } finally {
      sem.release();
    }
  }

  @Test
  public void test_functions() {
    sem_get();
    try {
      VCTResult res = run("vct", "--chalice", "//examples/manual/functions.pvl");
      if (res.verdict != Verdict.Pass)
        fail("bad result : " + res.verdict);
    } finally {
      sem.release();
    }
  }

  @Test
  public void test_witness() {
    sem_get();
    try {
      VCTResult res = run("vct", "--chalice", "--explicit", "--witness-inline",
          "//examples/manual/witness.pvl");
      if (res.verdict != Verdict.Pass)
        fail("bad result : " + res.verdict);
    } finally {
      sem.release();
    }
  }

  @Test
  public void test_list() {
    sem_get();
    try {
      VCTResult res = run("vct", "--chalice", "//examples/manual/list.pvl");
      if (res.verdict != Verdict.Pass)
        fail("bad result : " + res.verdict);
    } finally {
      sem.release();
    }
  }

  @Test
  public void test_fibonacci() {
    sem_get();
    try {
      VCTResult res = run("vct", "--chalice", "//examples/manual/fibonacci.pvl");
      if (res.verdict != Verdict.Pass)
        fail("bad result : " + res.verdict);
    } finally {
      sem.release();
    }
  }

  @Test
  public void test_array() {
    sem_get();
    try {
      VCTResult res = run("vct", "--chalice",
          "//examples/manual/zero_array.pvl");
      if (res.verdict != Verdict.Pass)
        fail("bad result : " + res.verdict);
    } finally {
      sem.release();
    }
  }

  @Test
  public void test_set_solution() {
    sem_get();
    try {
      VCTResult res = run("vct", "--chalice", "--inline",
          "//examples/manual/SetSolution.pvl");
      if (res.verdict != Verdict.Pass)
        fail("bad result : " + res.verdict);
    } finally {
      sem.release();
    }
  }

  @Test
  public void test_tree_solution() {
    sem_get();
    try {
      VCTResult res = run("vct", "--chalice",
          "//examples/manual/TreeSolution.pvl");
      if (res.verdict != Verdict.Pass)
        fail("bad result : " + res.verdict);
    } finally {
      sem.release();
    }
  }

  @Test
  public void test_list_solution() {
    sem_get();
    try {
      VCTResult res = run("vct", "--chalice", "--no-context",
          "//examples/manual/ListSolution.pvl");
      if (res.verdict != Verdict.Pass)
        fail("bad result : " + res.verdict);
    } finally {
      sem.release();
    }
  }

}
