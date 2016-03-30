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
  public void test_example1_err() {
    sem_get();
    try {
      VCTResult res = run("vct", "--silver=silicon", "--no-context",
          "//examples/manual/main.pvl", "//examples/manual/permissions.pvl");
      res.mustSay("assert.failed:assertion.false");

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
      VCTResult res = run("vct", "--silver=silicon", "--no-context",
          "//examples/manual/loop.pvl", "//examples/manual/permissions.pvl");
      if (res.verdict != Verdict.Pass)
        fail("bad result : " + res.verdict);
    } finally {
      sem.release();
    }
  }

  @Test
  public void test_example3_err() {
    sem_get();
    try {
      VCTResult res = run("vct", "--silver=silicon",
          "//examples/manual/parameters1.pvl",
          "//examples/manual/permissions.pvl");
      res.mustSay("assignment.failed:insufficient.permission");
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
      VCTResult res = run("vct", "--silver=silicon",
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
      VCTResult res = run("vct", "--silver=silicon", "//examples/manual/functions.pvl");
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
      VCTResult res = run("vct", "--silver=silicon", "//examples/manual/list.pvl");
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
      VCTResult res = run("vct", "--silver=silicon", "//examples/manual/fibonacci.pvl");
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
      VCTResult res = run("vct", "--silver=silicon_qp",
          "//examples/manual/zero_array.pvl");
      if (res.verdict != Verdict.Pass)
        fail("bad result : " + res.verdict);
    } finally {
      sem.release();
    }
  }

  @Test
  public void test_set_solution() {
    if (!Configuration.getHome().resolve("src/tex/homework/README").toFile().exists()){
      return;
    }
    sem_get();
    try {
      VCTResult res = run("vct", "--silver=silicon_qp", "--inline",
          "//src/tex/homework/SetSolution.pvl");
      if (res.verdict != Verdict.Pass)
        fail("bad result : " + res.verdict);
    } finally {
      sem.release();
    }
  }

  @Test
  public void test_tree_solution() {
    if (!Configuration.getHome().resolve("src/tex/homework/README").toFile().exists()){
      return;
    }
    sem_get();
    try {
      VCTResult res = run("vct", "--silver=silicon",
          "//src/tex/homework/TreeSolution.pvl");
      if (res.verdict != Verdict.Pass)
        fail("bad result : " + res.verdict);
    } finally {
      sem.release();
    }
  }

  @Test
  public void test_list_solution() {
    if (!Configuration.getHome().resolve("src/tex/homework/README").toFile().exists()){
      return;
    }
    sem_get();
    try {
      VCTResult res = run("vct", "--silver=silicon", "--no-context",
          "//src/tex/homework/ListSolution.pvl");
      if (res.verdict != Verdict.Pass)
        fail("bad result : " + res.verdict);
    } finally {
      sem.release();
    }
  }

  @Test
  public void test_set_solution2015() {
    if (!Configuration.getHome().resolve("src/tex/homework/README").toFile().exists()){
      return;
    }
    sem_get();
    try {
      VCTResult res = run("vct", "--silver=silicon_qp", "--inline",
          "//src/tex/homework/SetSolution2015.pvl");
      if (res.verdict != Verdict.Pass)
        fail("bad result : " + res.verdict);
    } finally {
      sem.release();
    }
  }

  @Test
  public void test_tree_solution2015() {
    if (!Configuration.getHome().resolve("src/tex/homework/README").toFile().exists()){
      return;
    }
    sem_get();
    try {
      VCTResult res = run("vct", "--silver=silicon",
          "//src/tex/homework/TreeSolution2015.pvl");
      if (res.verdict != Verdict.Pass)
        fail("bad result : " + res.verdict);
    } finally {
      sem.release();
    }
  }

  @Test
  public void test_list_solution2015() {
    if (!Configuration.getHome().resolve("src/tex/homework/README").toFile().exists()){
      return;
    }
    sem_get();
    try {
      VCTResult res = run("vct", "--silver=silicon", "--no-context",
          "//src/tex/homework/ListSolution2015.pvl");
      if (res.verdict != Verdict.Pass)
        fail("bad result : " + res.verdict);
    } finally {
      sem.release();
    }
  }

  @Test
  public void test_zero_array_pvl() {
    sem_get();
    try {
      VCTResult res = run("vct", "--silver=silicon_qp", "--no-context", "//doc/examples/zero_array_ic.pvl");
      if (res.verdict != Verdict.Pass)
        fail("bad result : " + res.verdict);
    } finally {
      sem.release();
    }
  }

  @Test
  public void test_zero_matrix_pvl() {
    sem_get();
    try {
      VCTResult res = run("vct", "--silver=silicon_qp", "--no-context", "//doc/examples/zero_matrix_ic.pvl");
      if (res.verdict != Verdict.Pass)
        fail("bad result : " + res.verdict);
    } finally {
      sem.release();
    }
  }

}
