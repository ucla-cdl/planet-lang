#' Creates Instance of Experiment Object  
#'
#' @param tasks List of Task objects, which represent the activities the participants will complete
#' @param conditions List of condition objects, which represent a variation of the independent variables being tested
#' @param trials List of trial objects, which represent an instance of a task completed by a single participant 
#'
#' @return An Experiment object 
#'
#' @examples
#' exp <- Experiment()
#' @import methods
#' @export
# Define constructor
Experiment <- function() {
  # TODO: Set default values for the pivs
  # Validate and create an instance of the class
  new("Experiment", tasks=list(), conditions=list(), trials=list())
}

#' @export
# toString for Experiment
# @prints tasks in this Experiment
setMethod(
  f = "show",
  signature = "Experiment",
  definition = function(object) {
    cat("Experiment Object:\n")
    cat("tasks:", unlist(object@tasks), "\n")
    cat("conditions:", unlist(object@conditions), "\n")
    cat("trials:", unlist(object@trials), "\n")
  }
)


# Define Experiment class
setClass(
  Class = "Experiment",
  slots = list(
    tasks = "list",
    conditions = "list",
    trials = "list" # for now -- likely want to have own class/data structure
  )
)


