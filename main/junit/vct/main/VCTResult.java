package vct.main;

import static org.junit.Assert.fail;
import hre.io.Message;
import hre.util.TestReport.Verdict;

import java.util.ArrayList;
import java.util.List;

class VCTResult {
  public Verdict verdict=null;
  public final List<Message> log=new ArrayList<Message>();
  public void mustSay(String string) {
    for(Message msg:log){
      if (msg.getFormat().equals("stdout: %s")||msg.getFormat().equals("stderr: %s")){
        if (((String)msg.getArg(0)).indexOf(string)>=0) return;
      }
    }
    fail("expected output "+string+" not found");
  };
  public void checkVerdict(Verdict res){
    if (verdict != res) fail("bad result : "+verdict);
  }
}