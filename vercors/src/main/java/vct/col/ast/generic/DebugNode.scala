package vct.col.ast.generic

import java.lang.reflect.Field
import java.util

import scala.collection.JavaConverters._
import scala.collection.Iterable
import hre.lang.System.Output

import scala.collection.mutable.ArrayBuffer

trait DebugNode {
  def debugTreeChildrenFields: Iterable[String]
  def debugTreePropertyFields: Iterable[String]

  private def indent_str(indent: Int): String = {
    var line = ""

    for(_ <- 0 until indent) {
      line += "  "
    }

    line
  }

  private def getReflectionField(obj: AnyRef, fieldName: String): Field = {
    var cls: Class[_] = obj.getClass

    while(cls != null) {
      try {
        return cls.getDeclaredField(fieldName)
      } catch {
        case e: NoSuchFieldException =>
          cls = cls.getSuperclass
      }
    }

    null
  }

  private def getField(obj: AnyRef, fieldName: String): AnyRef = {
    val field = getReflectionField(obj, fieldName)
    field.setAccessible(true)
    field.get(obj)
  }

  private def shouldBeShortcut[T1, T2](obj: AnyRef): Boolean = obj match {
    case null => true
    case node: DebugNode => node.isOnlyShortcut
    case map: util.HashMap[T1, T2] => map.isEmpty
    case arr: Array[T1] => arr.isEmpty
    case arr: util.ArrayList[T1] => arr.isEmpty
    case list: List[T1] => list.isEmpty
    case opt: Option[T1] => opt.isEmpty
    case map: util.Hashtable[T1, T2] => map.isEmpty
    case arr: ArrayBuffer[T1] => arr.isEmpty
    case _ => false
  }

  private def isOnlyShortcut: Boolean = {
    for(property <- debugTreeChildrenFields) {
      if(!shouldBeShortcut(getField(this, property))) {
        return false
      }
    }

    true
  }

  private def getShortcut[T1, T2](obj: AnyRef): String = obj match {
    case null => "null"
    case node: DebugNode if node.isOnlyShortcut => "(" + node.first_line + ")"
    case map: util.HashMap[T1, T2] if map.isEmpty => "{}"
    case arr: Array[T1] if arr.isEmpty => "[]"
    case arr: util.ArrayList[T1] if arr.isEmpty => "[]"
    case list: List[T1] if list.isEmpty => "[]"
    case opt: Option[T1] if opt.isEmpty => "None"
    case map: util.Hashtable[T1, T2] if map.isEmpty => "{}"
    case arr: ArrayBuffer[T1] if arr.isEmpty => "[]"
    case _ => null
  }

  private def dump[T1, T2](indent: Int, obj: Object, prefix: String): Unit = {
    obj match {
      case node: DebugNode =>
        node.dump(indent, prefix)
      case map: util.HashMap[T1, T2] =>
        Output("%s", indent_str(indent) + prefix + "Map")
        for (entry <- map.entrySet().asScala) {
          dump(indent + 1, entry.getValue.asInstanceOf[Object], "- " + entry.getKey.toString + ": ")
        }
      case map: util.Hashtable[T1, T2] =>
        Output("%s", indent_str(indent) + prefix + "Map")
        for (entry <- map.entrySet().asScala) {
          dump(indent + 1, entry.getValue.asInstanceOf[Object], "- " + entry.getKey.toString + ": ")
        }
      case arr: Array[T1] =>
        Output("%s", indent_str(indent) + prefix + "List")
        for (value <- arr) {
          dump(indent + 1, value.asInstanceOf[Object], "- ")
        }
      case arr: util.ArrayList[T1] =>
        Output("%s", indent_str(indent) + prefix + "List")
        for (value <- arr.asScala) {
          dump(indent + 1, value.asInstanceOf[Object], "- ")
        }
      case arr: ArrayBuffer[T1] =>
        Output("%s", indent_str(indent) + prefix + "List")
        for (value <- arr) {
          dump(indent + 1, value.asInstanceOf[Object], "- ")
        }
      case list: List[T1] =>
        Output("%s", indent_str(indent) + prefix + "List")
        for (value <- list) {
          dump(indent + 1, value.asInstanceOf[Object], "- ")
        }
      case opt: Option[T1] =>
        dump(indent, opt.get.asInstanceOf[Object], prefix)
      case _ =>
        Output("%s", indent_str(indent) + prefix + obj.getClass.getSimpleName + "???")
    }
  }

  private def first_line: String = {
    var first_line = this.getClass.getSimpleName

    for(property <- debugTreePropertyFields) {
      first_line += " " + property + "="
      val value = getField(this, property)
      if(value == null) {
        first_line += "null"
      } else {
        first_line += value.toString.replace("\n", "\\n")
      }
    }

    for(property <- debugTreeChildrenFields) {
      val value = getField(this, property)
      if(shouldBeShortcut(value)) {
        first_line += " " + property + "="
        first_line += getShortcut(value)
      }
    }

    first_line
  }

  private def dump(indent: Int, prefix: String = ""): Unit = {
    Output(indent_str(indent) + prefix + first_line)

    for(property <- debugTreeChildrenFields) {
      val value = getField(this, property)
      if(!shouldBeShortcut(value)) {
        dump(indent+1, value, property+": ")
      }
    }
  }

  def dump(): Unit = {
    dump(0)
  }
}
