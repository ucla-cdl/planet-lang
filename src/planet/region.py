from dataclasses import dataclass

@dataclass
class DesignRegion:
    """Represents a region in the design space. For example, 
    it might represent a subset of the first 2 trials in a 4 trial design."""
    width:int
    height:int
    stride:list[int]