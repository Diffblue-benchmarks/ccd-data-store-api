/**
 * @name Aggressive project-specific SQL injection detection
 * @description More aggressive SQL injection detection for demonstration
 *   purposes
 * @precision low
 * @kind path-problem
 * @problem.severity error
 * @id ccd-data-store-api/specialized-sql-injection
 */

import semmle.code.java.Expr
import semmle.code.java.dataflow.FlowSources
import DataFlow::PathGraph

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

from 
  DataFlow::Node source, DataFlow::Node sink,
  AggressiveSQLInjectionFlow config
where config.hasFlow(source, sink)
select source, sink, "potential SQL injection: @."
