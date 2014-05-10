package vct.runtime;

public abstract class ForkJoinBase implements Runnable {

	private Thread t;
	
	public void fork(){
		if (t==null){
			t=new Thread(this);
			t.start();
		} else {
			throw new Error("task has already been forked");
		}
	}
	
	public void join(){
		if (t==null){
			throw new Error("tasks must be forked before they can be joined");
		} else {
			try {
	      t.join();
      } catch (InterruptedException e) {
      	throw new Error("unexpected interruption of join");
      }
		}
	}
}
