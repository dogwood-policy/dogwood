@LRY0000000000("")
forbid(
  principal,
  action,
  resource
) when {
  (true && ((({"*~": action}["*~"]) in (if true then [a::"w", action, principal] else [action, resource, action])) || true)) && true
};
