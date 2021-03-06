package org.batfish.representation.cisco;

import org.batfish.common.Warnings;
import org.batfish.datamodel.Configuration;
import org.batfish.datamodel.routing_policy.statement.Comment;
import org.batfish.datamodel.routing_policy.statement.Statement;

public class RoutePolicyComment extends RoutePolicySetStatement {

   /**
    *
    */
   private static final long serialVersionUID = 1L;

   private String _text;

   public RoutePolicyComment(String text) {
      _text = text;
   }

   @Override
   protected Statement toSetStatement(
         CiscoConfiguration cc, Configuration c,
         Warnings w) {
      return new Comment(_text);
   }

}
