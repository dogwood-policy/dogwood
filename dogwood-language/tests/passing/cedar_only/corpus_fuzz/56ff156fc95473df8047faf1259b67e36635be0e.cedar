forbid(
  principal in a::"\0",
  action,
  resource
) when {
  (true && (a::"\0" has "")) && (resource has "{")
};
