#' Creates instance of Condition object
#'
#' @param name Name of condition with type string
#'
#' @return A Condition object
#'
#' @examples
#' condition = condition("latex")
#' @import methods

#' @export

# @returns Condition object
# @param name of task
condition <- function(name) {
    return(Condition(name))
}

# Define constructor
Condition <- function(name) {
  # Validate and create an instance of the class
  new("Condition", name=name)
}

# Specify conditions
# Define Condition class
setClass(
  Class = "Condition",
  slots = list(
    name = "character" 
    # Is there anything else that conditions contain besides a name?
  )
)
