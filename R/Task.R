#' Creates instance of Task object
#'
#' @param name Name of task with type string
#'
#' @return A Task object
#'
#' @examples
#' task = task("short editing task")
#' @import methods

#' @export
# @returns Task object
# @param name of task
task = function(name) {
    return(Task(name))
}


# Define constructor
Task <- function(name) {
  # Validate and create an instance of the class
  new("Task", name = name)
}

# Define Task class
setClass(
  Class = "Task",
  slots = list(
    name = "character"
  )
)

# toString for Task
# @prints tasks in this Task
setMethod(
  f = "show",
  signature = "Task",
  definition = function(object) {
    cat("Task Object:\n")
    cat("name:", unlist(object@name), "\n")
  }
)


