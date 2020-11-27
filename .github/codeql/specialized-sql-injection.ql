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
import DataFlow::PathGraph

predicate isMetaData(Expr expr) {
    exists(string pkg | expr.getType().(Class).hasQualifiedName(pkg, "MetaData"))
}

predicate isMetaDataP(Parameter param) {
    exists(string pkg | param.getType().(Class).hasQualifiedName(pkg, "MetaData"))
}

class AggressiveSQLInjectionFlow extends TaintTracking::Configuration {
    AggressiveSQLInjectionFlow() { this = "AggressiveSQLInjectionFlow" }

    override predicate isSource(DataFlow::Node source) {
        isMetaDataP(source.asParameter())
    }

    override predicate isSink(DataFlow::Node sink) {
        exists (MethodAccess m |
            m.getArgument(0) = sink.asExpr() and
            m.getMethod().getName() = "createNativeQuery")
    }

    override predicate isSanitizerIn(DataFlow::Node node) {
        exists (MethodAccess m |
            (node.asExpr().getParent() = m or
             m.getAnArgument() = node.asExpr()) and
            (m.getMethod().hasName("secure") or
             m.getMethod().hasName("addParameters") or
             m.getMethod().hasName("matches")))
    }

    override predicate isAdditionalTaintStep(DataFlow::Node source, DataFlow::Node sink) {        
        isMetaDataP(source.asParameter())
        and source.getLocation().getFile() = sink.getLocation().getFile()
        and exists(string filename |
            sink.hasLocationInfo(filename, 57, 44, 57, 107)
            and filename.matches("%SearchQueryFactoryOperation%"))
    }
}

from 
  DataFlow::PathNode source, DataFlow::PathNode sink,
  AggressiveSQLInjectionFlow config
where config.hasFlowPath(source, sink)
select sink.getNode(), source, sink, "Query might include data from $@.", source.getNode(), "this user input"
