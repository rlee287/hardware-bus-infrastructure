# Contribution Guidelines

Before submitting an issue, please note the following points:

* If you are reporting a bug, indicate which component(s) are broken, and ensure that your report contains a full MCVE (Minimal, Complete, and Verifiable Example).
* If you are requesting a feature, describe the feature in detail and provide a rationale for why it would be useful for other people.

Before submitting a pull request, please note the following points:

* Before starting work, make sure an issue has been created first, and assign yourself (or leave some other marker in the issue) to indicate that you are working on the issue. This reduces duplication of work.
* If you are submitting a bugfix, link the original issue(s) that you are aiming to fix. If you are adding new features, link the issue(s) in which the features were discussed.
* Public-facing interfaces to a module follow the naming conventions of the standard they are based on, but names for internal items do not have to. An example of this is that AXI-Stream properties use the terms "master" and "slave" in their name (as these are the names used in the specification), but internal signals should use alternative labels such as "tx"/"send" and "rx"/"receive".
* Pull requests are not merged until they have been reviewed and approved by at least one other person.