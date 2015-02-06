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
public class CARPTestD64 extends ToolTest {

  @Test
  public void test_par_id() {
    sem_get();
    try {
      VCTResult res = run("vct", "--silver=silicon_qp", "//examples/carp_D64/par-id.c");
      res.checkVerdict(Verdict.Pass);
    } finally {
      sem.release();
    }
  }
  @Test
  public void test_vector_add_c() {
    sem_get();
    try {
      VCTResult res = run("vct", "--silver=silicon_qp", "//examples/carp_D64/vector-add.c");
      res.checkVerdict(Verdict.Pass);
    } finally {
      sem.release();
    }
  }

  @Test
  public void test_vector_add_pvl() {
    sem_get();
    try {
      VCTResult res = run("vct", "--silver=silicon_qp", "//examples/carp_D64/vector-add.pvl");
      res.checkVerdict(Verdict.Pass);
    } finally {
      sem.release();
    }
  }

  @Test
  public void test_indep_loop_drf_c() {
    sem_get();
    try {
      VCTResult res = run("vct", "--silver=silicon_qp", "//examples/carp_D64/indep-loop-drf.c");
      res.checkVerdict(Verdict.Pass);
    } finally {
      sem.release();
    }
  }

  @Test
  public void test_forward_dep_drf_c() {
    sem_get();
    try {
      VCTResult res = run("vct", "--silver=silicon_qp", "//examples/carp_D64/forward-dep-drf.c");
      res.checkVerdict(Verdict.Pass);
    } finally {
      sem.release();
    }
  }

  @Test
  public void test_forward_dep_c() {
    sem_get();
    try {
      VCTResult res = run("vct", "--silver=silicon_qp", "//examples/carp_D64/forward-dep.c");
      res.checkVerdict(Verdict.Pass);
    } finally {
      sem.release();
    }
  }

  @Test
  public void test_forward_dep_e1_c() {
    sem_get();
    try {
      VCTResult res = run("vct", "--silver=silicon_qp", "//examples/carp_D64/forward-dep-e1.c");
      res.checkVerdict(Verdict.Fail);
    } finally {
      sem.release();
    }
  }

  @Test
  public void test_forward_dep_pvl() {
    sem_get();
    try {
      VCTResult res = run("vct", "--silver=silicon_qp", "--single-group", "//examples/carp_D64/forward-dep.pvl");
      res.checkVerdict(Verdict.Pass);
    } finally {
      sem.release();
    }
  }

  @Test
  public void test_forward_dep_noauto_pvl() {
    sem_get();
    try {
      VCTResult res = run("vct", "--silver=silicon_qp", "--single-group", "--disable-auto-barrier", "//examples/carp_D64/forward-dep-noauto.pvl");
      res.checkVerdict(Verdict.Pass);
    } finally {
      sem.release();
    }
  }

  @Test
  public void test_backward_dep_drf_c() {
    sem_get();
    try {
      VCTResult res = run("vct", "--silver=silicon_qp", "//examples/carp_D64/backward-dep-drf.c");
      res.checkVerdict(Verdict.Pass);
    } finally {
      sem.release();
    }
  }

  @Test
  public void test_backward_dep_c() {
    sem_get();
    try {
      VCTResult res = run("vct", "--silver=silicon_qp", "//examples/carp_D64/backward-dep.c");
      res.checkVerdict(Verdict.Pass);
    } finally {
      sem.release();
    }
  }

  @Test
  public void test_backward_dep_e1_c() {
    sem_get();
    try {
      VCTResult res = run("vct", "--silver=silicon_qp", "//examples/carp_D64/backward-dep-e1.c");
      res.checkVerdict(Verdict.Fail);
    } finally {
      sem.release();
    }
  }

  @Test
  public void test_kernel_example_pvl() {
    sem_get();
    try {
      VCTResult res = run("vct", "--silver=silicon_qp", "--single-group", "//examples/carp_D64/kernel-example.pvl");
      res.checkVerdict(Verdict.Pass);
    } finally {
      sem.release();
    }
  }

  @Test
  public void test_kernel_example_v2_pvl() {
    sem_get();
    try {
      VCTResult res = run("vct", "--silver=silicon_qp", "--single-group", "//examples/carp_D64/kernel-example-v2.pvl");
      res.checkVerdict(Verdict.Pass);
    } finally {
      sem.release();
    }
  }

  @Test
  public void test_kernel_example_v3_pvl() {
    sem_get();
    try {
      VCTResult res = run("vct", "--silver=silicon_qp", "--single-group", "--disable-auto-barrier", "//examples/carp_D64/kernel-example-v3.pvl");
      res.checkVerdict(Verdict.Pass);
    } finally {
      sem.release();
    }
  }

  @Test
  public void test_IterationExample() {
    sem_get();
    try {
      VCTResult res = run("vct", "--silver=silicon_qp", "//examples/carp_D64/IterationExample.java");
      res.checkVerdict(Verdict.Pass);
    } finally {
      sem.release();
    }
  }


  
}
