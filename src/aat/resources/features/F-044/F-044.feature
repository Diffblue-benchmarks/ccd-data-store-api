@F-044
Feature: F-044: Submit event creation as Case worker

  Background: Load test data for the scenario
    Given an appropriate test context as detailed in the test data source

  @S-278
  Scenario: must submit the event creation successfully for correct inputs
    Given a user with [an active profile in CCD]
    And a case that has just been created as in [Standard_Full_Case_Creation_Data]
    And a successful call [to get an event token for the case just created] as in [F-044-Prerequisite]
    When a request is prepared with appropriate values
    And the request [contains a case Id that has just been created as in Standard_Full_Case_Creation_Data]
    And the request [contains an event token for the case just created above]
    And it is submitted to call the [submit event creation as case worker] operation of [CCD Data Store]
    Then a positive response is received
    And the response [contains the updated case details, along with an HTTP 201 Created]
    And the response has all other details as expected

  @S-279 @Ignore # Response code mismatch, expected: 401, actual: 403
  Scenario: must return negative response when request does not provide valid authentication credentials
    Given a user with [an active profile in CCD]
    When a request is prepared with appropriate values
    And the request [does not provide valid authentication credentials]
    And it is submitted to call the [submit event creation as case worker] operation of [CCD Data Store]
    Then a negative response is received
    And the response [contains an HTTP 401 Forbidden]
    And the response has all other details as expected

  @S-280
  Scenario: must return negative response when request does not provide an authorised access
    Given a user with [an active profile in CCD]
    When a request is prepared with appropriate values
    And the request [does not provide authorised access to the operation]
    And it is submitted to call the [submit event creation as case worker] operation of [CCD Data Store]
    Then a negative response is received
    And the response [contains an HTTP 403 Forbidden]
    And the response has all other details as expected

  @S-281 @Ignore # This scenario is returning 400 instead of expected 404, linked to defect JIRA-6868
  Scenario: must return negative response when request contains a non-existing case reference
    Given a user with [an active profile in CCD]
    When a request is prepared with appropriate values
    And the request [contains a non-existing case reference]
    And it is submitted to call the [submit event creation as case worker] operation of [CCD Data Store]
    Then a negative response is received
    And the response [contains an HTTP 404 'Bad Request']
    And the response has all other details as expected

  @S-282
  Scenario: must return 409 when case is altered out of the transaction
    Given a user with [an active profile in CCD]
    And a case that has just been created as in [Standard_Full_Case_Creation_Data]
    And a successful call [to get an event token for the case just created] as in [F-044-Prerequisite]
    And another successful call [to update that case with the token just created] as in [F-044-Prerequisite_CaseUpdate]
    When a request is prepared with appropriate values
    And the request [contains a case Id that has just been updated above]
    And the request [contains token created above which is no longer valid for current version of case]
    And it is submitted to call the [submit event creation as case worker] operation of [CCD Data Store]
    Then a negative response is received
    And the response [contains an HTTP 409 'Conflict']
    And the response has all other details as expected

  @S-283
  Scenario: must return 422 when event submission has failed
    Given a user with [an active profile in CCD]
    And a case that has just been created as in [Standard_Full_Case_Creation_Data]
    And a successful call [to get an event token for the case just created] as in [F-044-Prerequisite]
    When a request is prepared with appropriate values
    And the request [contains a case Id that has just been created as in Standard_Full_Case_Creation_Data]
    And the request [contains an event token for the case just created above]
    And the request [contains an invalid event Id for the pre-state conditions]
    And it is submitted to call the [submit event creation as case worker] operation of [CCD Data Store]
    Then a negative response is received
    And the response [contains an HTTP 422 'Unprocessable Entity']
    And the response has all other details as expected

  @S-277 @Ignore # This scenario is returning 403 instead of expected 404, linked to defect JIRA-6917
  Scenario: must return 404 when request contains a non-existing jurisdiction Id
    Given a user with [an active profile in CCD]
    When a request is prepared with appropriate values
    And the request [contains a non-existing jurisdiction Id]
    And it is submitted to call the [submit event creation as case worker] operation of [CCD Data Store]
    Then a negative response is received
    And the response [contains an HTTP 404 'Not Found']
    And the response has all the details as expected

  @S-560 @Ignore # This scenario is returning 400 instead of expected 404, linked to defect JIRA-6918
    Scenario: must return 404 when request contains a non-existing case type
    Given a user with [an active profile in CCD]
    When a request is prepared with appropriate values
    And the request [contains a non-existing case type]
    And it is submitted to call the [submit event creation as case worker] operation of [CCD Data Store]
    Then a negative response is received
    And the response [contains an HTTP 404 'Not Found']
    And the response has all the details as expected

    @S-113 @Ignore
    Scenario: should not update a case if the caseworker has 'C' access on CaseType
    <already implemented previously. will be refactored later.>

    @S-114 @Ignore
    Scenario: should not update a case if the caseworker has 'CR' access on CaseType
    <already implemented previously. will be refactored later.>

    @S-115 @Ignore
    Scenario: should not update a case if the caseworker has 'D' access on CaseType
    <already implemented previously. will be refactored later.>

    @S-116 @Ignore
    Scenario: should not update a case if the caseworker has 'R' access on CaseType
    <already implemented previously. will be refactored later.>

    @S-117 @Ignore
    Scenario: should progress case state
    <already implemented previously. will be refactored later.>

    @S-118 @Ignore
    Scenario: should update a case if the caseworker has 'CRUD' access on CaseType
    <already implemented previously. will be refactored later.>

    @S-119 @Ignore
    Scenario: should update a case if the caseworker has 'CU' access on CaseType
    <already implemented previously. will be refactored later.>

    @S-120 @Ignore
    Scenario: should update a case if the caseworker has 'RU' access on CaseType
    <already implemented previously. will be refactored later.>

    @S-121 @Ignore
    Scenario: should update a case if the caseworker has 'U' access on CaseType
    <already implemented previously. will be refactored later.>

    @S-122 @Ignore
    Scenario: should update a single case field
    <already implemented previously. will be refactored later.>
