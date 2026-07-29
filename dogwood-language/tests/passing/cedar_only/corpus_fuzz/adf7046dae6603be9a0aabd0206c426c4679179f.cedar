@rhhhhhhhhh("++++++++++++++++++jp1FF\0")
permit(
  principal in a::"\0\0\0\0\0Debian \0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0B",
  action == Action::"",
  resource in a::"\0\0\0\0\0Debian \0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0B"
) when {
  (true && ([""].contains(""))) && ((if (resource in principal) then [ip("42.42.65.210"), ip("99.44.63.110")] else [ip("2b2b:2b2b:2b2b:2b2b:2b2b:2b2b:2b2b:2b2b/43"), ip("2b2b:2b2+:2b2b:2b2b:2b2b:2b2b:2b2b:2b2b/43"), ip("2b2b:2b2b:2b2b:2b2b:2b2b:2b2b:2b2b:2b2b/43")]).containsAny([ip(""), ip(""), ip("")]))
};
