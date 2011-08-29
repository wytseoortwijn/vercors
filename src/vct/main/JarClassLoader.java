package vct.main;

import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.util.jar.JarEntry;
import java.util.jar.JarFile;
import static hre.System.*;

public class JarClassLoader extends ClassLoader {
    private final JarFile jar;

    public JarClassLoader(File jarFile) throws IOException {
        super(JarClassLoader.class.getClassLoader()); //calls the parent class loader's constructor
        jar = new JarFile(jarFile);
    }
    
    protected synchronized Class loadClass(String className, boolean resolve) throws ClassNotFoundException {
      Class cls = findLoadedClass(className);
      if (cls != null) {
        return cls;
      }
      //System.err.printf("trying to load %s%n",className);
      String clsFile = className.replace('.', '/') + ".class";
      JarEntry entry = jar.getJarEntry(clsFile);
      if (entry==null){
        //System.err.printf("cannot find %s in jar%n",className);
        return super.loadClass(className,resolve);
      }
      InputStream is;
      try {
        is = jar.getInputStream(entry);
      } catch (IOException e) {
        throw new ClassNotFoundException("IOException: "+e);
      }
      // 3. get bytes for class
      //System.err.printf("size is %d (%d)%n", entry.getSize(),entry.getCompressedSize());
      byte[] classBytes = new byte[(int) entry.getSize()];
      try {
          int read=0;
          int expect=(int)entry.getSize();
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

/*
    public Class findClass(String className) {
        byte classByte[];
        Class result = null;

        result = (Class) classes.get(className); //checks in cached classes
        if (result != null) {
            return result;
        }

        try {
            return findSystemClass(className);
        } catch (Exception e) {
        }

        try {
            JarFile jar = new JarFile(jarFile);
            JarEntry entry = jar.getJarEntry(className + ".class");
            InputStream is = jar.getInputStream(entry);
            ByteArrayOutputStream byteStream = new ByteArrayOutputStream();
            int nextValue = is.read();
            while (-1 != nextValue) {
                byteStream.write(nextValue);
                nextValue = is.read();
            }

            classByte = byteStream.toByteArray();
            result = defineClass(className, classByte, 0, classByte.length, null);
            classes.put(className, result);
            return result;
        } catch (Exception e) {
            return null;
        }
    }
*/
    
}

