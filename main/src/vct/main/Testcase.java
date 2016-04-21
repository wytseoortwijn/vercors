package vct.main;

import java.nio.file.Path;
import java.util.ArrayList;
import java.util.HashSet;

class Testcase {
  public HashSet<String> tools=new HashSet();
  public ArrayList<String> options=new ArrayList();
  public HashSet<Path> files=new HashSet();
  public String verdict="Pass";
  public HashSet<String> suites=new HashSet();
}