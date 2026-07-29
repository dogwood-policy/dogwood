@w0000W000000000("")
forbid(
  principal,
  action == Action::"action",
  resource
) when {
  (true && (action in action)) && (resource in principal)
};
