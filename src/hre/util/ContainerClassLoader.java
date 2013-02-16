package hre.util;

import hre.io.Container;

import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.util.jar.JarEntry;
import java.util.jar.JarFile;
import static hre.System.*;

public class ContainerClassLoader extends ClassLoader {
    private final Container source;

    public ContainerClassLoader(Container source) throws IOException {
        super(ContainerClassLoader.class.getClassLoader()); //calls the parent class loader's constructor
        this.source=source;
    }
    
    protected synchronized Class loadClass(String className, boolean resolve) throws ClassNotFoundException {
      Class cls = findLoadedClass(className);
      if (cls != null) {
        return cls;
      }
      Debug("trying to load %s",className);
      String clsFile = className.replace('.', '/') + ".class";
      if (!source.contains(clsFile)){
        Debug("using parent loader for %s",className);
        return super.loadClass(className,resolve);
      }
      Debug("using ContainerClassLoader for %s",className);
      InputStream is;
      try {
        is = source.read(clsFile);
      } catch (IOException e) {
        throw new ClassNotFoundException("IOException: "+e);
      }
      // 3. get bytes for class
      //System.err.printf("size is %d (%d)%n", entry.getSize(),entry.getCompressedSize());
      byte[] classBytes = new byte[(int) source.size(clsFile)];
      try {
          int read=0;
          int expect=(int)source.size(clsFile);
          while(read<expect){
            int tmp=is.read(classBytes,read,(expect-read));
            if (tmp==0) Fail("not enough data");
            read+=tmp;
            //System.err.printf("got %d of %d bytes%n", read,expect);
          }
      } catch (IOException e) {
          Fail("ERROR loading class file: " + e);
      }
      // 4. turn the byte array into a Class
      try {
          cls = defineClass(className, classBytes, 0, classBytes.length);
          if (resolve) {
              resolveClass(cls);
          }
      }
      catch (SecurityException e) { 
          // loading core java classes such as java.lang.String
          // is prohibited, throws java.lang.SecurityException.
          // delegate to parent if not allowed to load class
          cls = super.loadClass(className, resolve);
      }
      //System.err.printf("completed loading %s%n",className);
      return cls;
    }
    
    @Override
    protected String findLibrary(String libname){
    	String fullname=System.mapLibraryName(libname);
    	return source.findFile(fullname);
    }

}

