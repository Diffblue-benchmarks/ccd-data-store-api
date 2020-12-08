/**
 * @name Aggressive project-specific SQL injection detection
 * @description More aggressive SQL injection detection for demonstration
 *   purposes
 * @precision low
 * @kind path-problem
 * @problem.severity error
 * @id ccd-data-store-api/specialized-sql-injection
 */

import java
import semmle.code.java.dataflow.FlowSources
import semmle.code.java.security.Validation
import semmle.code.java.security.QueryInjection
import semmle.code.java.dataflow.internal.TaintTrackingUtil
import semmle.code.java.dataflow.internal.DataFlowUtil
import DataFlow
import DataFlow::PathGraph

predicate flowsThroughOptional(DataFlow::Node source, DataFlow::Node sink) {
    exists (MethodAccess call |
        sink.asExpr() = call
        and call.getQualifier() = source.asExpr()
        and call.getMethod().getName() = "orElse"
        and call.getMethod().getDeclaringType().getErasure().(ClassOrInterface).hasQualifiedName("java.util", "Optional")
    )
}

class BasicSQLInjectionFlow extends TaintTracking::Configuration {
   BasicSQLInjectionFlow() {
     this="BSIF"
    }

    override predicate isSource(DataFlow::Node source) {
        source instanceof RemoteFlowSource
        or
        source.asParameter().getType().(ClassOrInterface).hasQualifiedName(_, "MetaData")
    }

    override predicate isSink(DataFlow::Node sink) {
        exists (MethodAccess m |
            m.getAnArgument() = sink.asExpr() and
            m.getMethod().getName() = "createNativeQuery")
    }

    override predicate isSanitizer(DataFlow::Node node) {
        node.getType() instanceof PrimitiveType or
        node.getType() instanceof BoxedType or
        node.getType() instanceof NumberType
    }

    override predicate isAdditionalTaintStep(DataFlow::Node source, DataFlow::Node sink) {
        flowsThroughOptional(source, sink)
        or
        exists(MethodAccess call |
          sink.asExpr() = call and
          call.getQualifier() = source.asExpr() and
          call.getMethod().getName() = "getSortDirection" and
          call.getMethod().getDeclaringType().(ClassOrInterface).hasQualifiedName(_, "MetaData"))
    }
}

predicate preciseLocation(string description, DataFlow::Node node) {
  exists (string file, int startLine, int startColumn, int endLine, int endColumn |
    node.asExpr().hasLocationInfo(file, startLine, startColumn, endLine, endColumn) and
    description = file + ":" + startLine.toString() + ":" + startColumn.toString() + ":" + endLine.toString() + ":" + endColumn.toString())
}

query predicate allEdges(string src, string tgt) {
  exists (DataFlow::Node s, DataFlow::Node t |
    preciseLocation(src, s) and
    preciseLocation(tgt, t) and
    localTaintStep(s, t)
  )
}


from DataFlow::PathNode source, DataFlow::PathNode sink, BasicSQLInjectionFlow config
where config.hasFlowPath(source, sink)
select sink.getNode(), source, sink, "User input from $@.", source.getNode(), "here"
