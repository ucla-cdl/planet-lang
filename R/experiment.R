#' Creates Instance of Experiment Object  
#'
#' @param tasks List of Task objects, which represent the activities the participants will complete
#' @param conditions List of condition objects, which represent a variation of the independent variables being tested
#' @param trials List of trial objects, which represent an instance of a task completed by a single participant 
#'
#' @return An Experiment object 
#' @export
#' @import methods
#'
#' @examples
#' x <- "alfa,bravo,charlie,delta"
#' strsplit1(x, split = ",")
# Define Experiment class
setClass(
  Class = "Experiment",
  slots = list(
    tasks = "list",
    conditions = "list",
    trials = "list" # for now -- likely want to have own class/data structure
  )
)

# Define constructor
Experiment <- function() {
  # TODO: Set default values for the pivs
  # Validate and create an instance of the class
  new("Experiment", tasks=list(), conditions=list(), trials=list())
}
