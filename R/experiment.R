#' Creates Instance of Experiment Object  
#'
#'
#' @return An Experiment object 
#'
#' @examples
#' exp <- experiment()
#' @import methods
#' @export

# public method that calls Experiment constructor 
experiment <- function() {
  Experiment()
}

# Define constructor
Experiment <- function() {
  # TODO: Set default values for the pivs
  # Validate and create an instance of the class
  new("Experiment", tasks=list(), conditions=list(), trials=list())
}

# Define Experiment class
setClass(
  Class = "Experiment",
  slots = list(
    tasks = "list",
    conditions = "list",
    trials = "list" # for now -- likely want to have own class/data structure
  )
)

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





