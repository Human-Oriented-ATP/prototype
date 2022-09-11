# human-style
## To-do
- Find a better way of writing commands involving a Tableau with a single box (constant repeating boxToTabMove isn't fun, and constantly specifying 0 for "first box" isn't either, even after we boxToTabMove everything at the top of the file)
- Implement a more legitimate system of representing Free variables in library statements for matching purposes via the HExpr system
- Think about how the variables in the QZone should behave when it comes to library equivalences, one-way implications and - probably most relevantly - existence solving.
- Implement lower-level library moves which clearly distinguish equivalences and implications, as explained in one of the comments in NewMoves
- Improve the system of finding/using ExternalName's when peeling and printing
- Think about and implement existence solving via the library
- Improve how we track freeVariables in expressions (probably just use a function to compute free variables from an expression rather than storing - it's not THAT slow. Otherwise, compute it whenever we need to update)
- Parser for inputting LibraryEquivalence's (bit of a nightmare right now)
- (longer term) Think about and implement existence solving in a more thorough way as discussed in document