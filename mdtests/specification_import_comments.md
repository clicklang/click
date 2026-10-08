# Comments in a specification and its imported module

```click
// The loader must ignore: import "missing.click";
/* Comments may precede imports and contain unmatched delimiters: } ' " */
import "specification_import_comments_model.click";

theorem commented_identity_works(x: int32) {
    ensures commented_identity(x) == x by {
        unfold(commented_identity(x)); // another } ignored
        normalize();
    }
}
```

```expect
pass
```
