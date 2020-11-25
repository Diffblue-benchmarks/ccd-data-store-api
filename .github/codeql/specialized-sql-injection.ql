/**
 * @name Aggressive project-specific SQL injection detection
 * @kind path-problem
 * @problem.severity error
 * @id ccd-data-store-api/specialized-sql-injection
 */

import java
import semmle.code.java.dataflow.TaintTracking

class AggressiveSQLInjectionFlow extends TaintTracking::Configuration {
    AggressiveSQLInjectionFlow() { this = "AggressiveSQLInjectionFlow" }

    override predicate isSource(DataFlow::Node source) {
        exists (Parameter p | source.asParameter() = p)
    }

    override predicate isSink(DataFlow::Node sink) {
        exists (VirtualMethodAccess m |
            m.getArgument(0) = sink.asExpr() and
            m.getMethod().getName() = "createNativeQuery"
            )
    }

    override predicate isAdditionalTaintStep(DataFlow::Node source, DataFlow::Node sink) {
        exists (VirtualMethodAccess m |
            (m.getAnArgument() = source.asExpr()
             or source.asExpr().getParent() = m)
            and m = sink.asExpr())        
    }
}

from AggressiveSQLInjectionFlow config,
  DataFlow::Node source, DataFlow::Node sink
where config.hasFlow(source, sink)
select source, source, sink, "potential SQL injection"