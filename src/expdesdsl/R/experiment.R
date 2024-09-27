#' Creates Instance of Experiment Object  
#'
#' @return An Experiment object 
#'
#' @examples
#' exp <- experiment()
#' @import methods
#' @export

# public method that calls Experiment constructor 
experiment <- function(name) {
  Experiment(name)
}

# Define constructor
Experiment <- function(name) {
  # TODO: Set default values for the pivs
  # Validate and create an instance of the class
  new("Experiment", name=name, tasks=list(), conditions=list(), trials=list())
}

# Define Experiment class
setClass(
  Class = "Experiment",
  slots = list(
    name = "character",
    tasks = "list",
    conditions = "list",
    trials = "list" # TODO: for now -- likely want to have own class/data structure
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


# this method needs a lot of work
setGeneric("assign_condition_order", function(object) standardGeneric("assign_condition_order"))

setMethod(
  f = "assign_condition_order",
  signature = "Experiment",
  definition = function(object) {
    # Shuffle condition order
    order = sample(object@conditions)
    
    return(order) 
  }
)





