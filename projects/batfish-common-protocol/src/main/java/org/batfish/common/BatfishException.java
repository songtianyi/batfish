package org.batfish.common;

import com.fasterxml.jackson.annotation.JsonCreator;
import com.fasterxml.jackson.annotation.JsonIgnore;
import com.fasterxml.jackson.annotation.JsonProperty;
import com.fasterxml.jackson.annotation.JsonValue;
import java.io.Serializable;
import java.util.Arrays;
import java.util.List;
import org.apache.commons.lang.exception.ExceptionUtils;
import org.batfish.datamodel.answers.AnswerElement;

/**
 * Thrown as a fatal exception. When caught, Batfish should perform any
 * necessary cleanup and terminate gracefully with a non-zero exit status. A
 * BatfishException should always contain a detail message.
 */
public class BatfishException extends RuntimeException {

   public static class BatfishStackTrace implements Serializable, AnswerElement {

      /**
       * 
       */
      private static final long serialVersionUID = 1L;

      private static final String LINES_VAR = "answer";

      private final BatfishException _exception;

      private final List<String> _lines;

      public BatfishStackTrace(BatfishException exception) {
         String stackTrace = ExceptionUtils.getFullStackTrace(exception)
               .replace("\t", "   ");
         _lines = Arrays.asList(stackTrace.split("\\n"));
         _exception = exception;
      }

      @JsonCreator
      public BatfishStackTrace(@JsonProperty(LINES_VAR) List<String> lines) {
         _lines = lines;
         _exception = null;
      }

      @JsonIgnore
      public BatfishException getException() {
         return _exception;
      }

      @JsonProperty(LINES_VAR)
      public List<String> getLineMap() {
         return _lines;
      }

      @Override
      public String prettyPrint() {
         return String.join("\n", _lines);
      }
   }

   private static final long serialVersionUID = 1L;

   /**
    * Constructs a BatfishException with a detail message
    *
    * @param msg
    *           The detail message
    */
   public BatfishException(String msg) {
      super(msg);
   }

   /**
    * Constructs a BatfishException with a detail message and a cause
    *
    * @param msg
    *           The detail message
    * @param cause
    *           The cause of this exception
    */
   public BatfishException(String msg, Throwable cause) {
      super(msg, cause);
   }

   @JsonValue
   public BatfishStackTrace getBatfishStackTrace() {
      return new BatfishStackTrace(this);
   }

}
