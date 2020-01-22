package uk.gov.hmcts.ccd.domain.model.common;

import org.junit.Before;
import org.junit.Test;
import org.springframework.http.HttpStatus;
import org.springframework.web.bind.annotation.ResponseStatus;
import uk.gov.hmcts.ccd.endpoint.exceptions.ApiException;

import javax.servlet.http.HttpServletRequest;
import java.util.Arrays;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import static org.hamcrest.Matchers.equalTo;
import static org.hamcrest.Matchers.is;
import static org.hamcrest.Matchers.notNullValue;
import static org.junit.Assert.assertThat;
import static org.mockito.Mockito.doReturn;
import static org.mockito.Mockito.mock;

public class HttpErrorTest {

    private static final String MESSAGE = "Error message";
    private static final String DETAILS = "Details of the error";
    private static final String PATH = "/some/rest/resource";
    private static final List<String> CALLBACK_ERRORS = Arrays.asList("Errors: E1", "Errors: E2");
    private static final List<String> CALLBACK_WARNINGS = Arrays.asList("Warnings: W1", "Warnings: W2");

    private HttpServletRequest request;

    @Before
    public void setUp() {
        request = mock(HttpServletRequest.class);
        doReturn(PATH).when(request).getRequestURI();
    }

    @Test
    public void shouldExtractExceptionNameFromException() {
        final HttpError error = new HttpError(new IllegalArgumentException(), request);

        assertThat(error.getException(), is(equalTo("java.lang.IllegalArgumentException")));
    }

    @Test
    public void shouldExtractTimestampFromException() {
        final HttpError error = new HttpError(new IllegalArgumentException(), request);

        assertThat(error.getTimestamp(), is(notNullValue()));
    }

    @Test
    public void shouldExtractStatusFromExceptionAnnotation_withCode() {
        final HttpError error = new HttpError(new TestCodeStatusException(), request);

        assertThat(error.getStatus(), is(equalTo(415)));
    }

    @Test
    public void shouldExtractStatusFromExceptionAnnotation_withValue() {
        final HttpError error = new HttpError(new TestValueStatusException(), request);

        assertThat(error.getStatus(), is(equalTo(404)));
    }

    @Test
    public void shouldExtractStatusFromStatus_withExceptionAnnotationAlsoProvided() {
        HttpStatus testStatus = HttpStatus.I_AM_A_TEAPOT;
        final HttpError error = new HttpError(new TestValueStatusException(), request, null, testStatus.value());

        // test Status has taken precedence over ResponseStatus annotation
        assertThat(error.getStatus(), is(equalTo(testStatus.value())));
    }

    @Test
    public void shouldExtractStatusFromStatus_withoutExceptionAnnotation() {
        HttpStatus testStatus = HttpStatus.I_AM_A_TEAPOT;
        // NB: NullPointerException has no ResponseStatus annotation
        final HttpError error = new HttpError(new NullPointerException(), request, null, testStatus.value());

        assertThat(error.getStatus(), is(equalTo(testStatus.value())));
    }

    @Test
    public void shouldExtractStatusFromDefault_withExceptionAnnotationThatsBlank() {
        final HttpError error = new HttpError(new TestBlankResponseStatusException(), request);

        assertThat(error.getStatus(), is(equalTo(HttpError.DEFAULT_STATUS)));
    }

    @Test
    public void shouldExtractStatusFromDefault_withExceptionAnnotationThatUses500Status() {
        final HttpError error = new HttpError(new Test500StatusException(), request);

        assertThat(error.getStatus(), is(equalTo(HttpError.DEFAULT_STATUS)));
    }

    @Test
    public void shouldExtractStatusFromDefault_with500Status() {
        // NB: NullPointerException has no ResponseStatus annotation
        final HttpError error = new HttpError(new NullPointerException(), request, null, 500);

        assertThat(error.getStatus(), is(equalTo(HttpError.DEFAULT_STATUS)));
    }

    @Test
    public void shouldExtractStatusFromDefault_withoutExceptionAnnotationNorStatus() {
        // NB: NullPointerException has no ResponseStatus annotation
        final HttpError error = new HttpError(new NullPointerException(), request, null, null);

        assertThat(error.getStatus(), is(equalTo(HttpError.DEFAULT_STATUS)));
    }

    @Test
    public void shouldExtractErrorFromExceptionAnnotation_withReason() {
        final HttpError error = new HttpError(new TestReasonException(), request);

        assertThat(error.getError(), is(equalTo("Some error reason")));
    }

    @Test
    public void shouldExtractErrorFromExceptionAnnotation_withCode() {
        final HttpError error = new HttpError(new TestCodeStatusException(), request);

        assertThat(error.getError(), is(equalTo(HttpStatus.UNSUPPORTED_MEDIA_TYPE.getReasonPhrase())));
    }

    @Test
    public void shouldExtractErrorFromExceptionAnnotation_withValue() {
        final HttpError error = new HttpError(new TestValueStatusException(), request);

        assertThat(error.getError(), is(equalTo(HttpStatus.NOT_FOUND.getReasonPhrase())));
    }

    @Test
    public void shouldExtractErrorFromStatus_withExceptionAnnotationAlsoProvided() {
        HttpStatus testStatus = HttpStatus.I_AM_A_TEAPOT;
        final HttpError error = new HttpError(new TestValueStatusException(), request, null, testStatus.value());

        // test Status has taken precedence over ResponseStatus annotation
        assertThat(error.getError(), is(equalTo(testStatus.getReasonPhrase())));
    }

    @Test
    public void shouldExtractErrorFromStatus_withoutExceptionAnnotation() {
        HttpStatus testStatus = HttpStatus.I_AM_A_TEAPOT;
        // NB: NullPointerException has no ResponseStatus annotation
        final HttpError error = new HttpError(new NullPointerException(), request, null, testStatus.value());

        assertThat(error.getError(), is(equalTo(testStatus.getReasonPhrase())));
    }

    @Test
    public void shouldExtractErrorFromDefault_withExceptionAnnotationThatsBlank() {
        final HttpError error = new HttpError(new TestBlankResponseStatusException(), request);

        assertThat(error.getError(), is(equalTo(HttpError.DEFAULT_ERROR)));
    }

    @Test
    public void shouldExtractErrorFromDefault_withExceptionAnnotationThatUses500Status() {
        final HttpError error = new HttpError(new Test500StatusException(), request);

        assertThat(error.getError(), is(equalTo(HttpError.DEFAULT_ERROR)));
    }

    @Test
    public void shouldExtractErrorFromDefault_with500Status() {
        // NB: IllegalArgumentException has no ResponseStatus annotation
        final HttpError error = new HttpError(new IllegalArgumentException(), request, null, 500);

        assertThat(error.getError(), is(equalTo(HttpError.DEFAULT_ERROR)));
    }

    @Test
    public void shouldExtractErrorFromDefault_withoutExceptionAnnotationNorStatus() {
        // NB: IllegalArgumentException has no ResponseStatus annotation
        final HttpError error = new HttpError(new IllegalArgumentException(), request);

        assertThat(error.getError(), is(equalTo(HttpError.DEFAULT_ERROR)));
    }

    @Test
    public void shouldExtractCatalogueResponseFromApiException() {
        // ARRANGE
        final Map<String, Object> expectedDetails = new HashMap<>();
        expectedDetails.put("test1", 1);
        expectedDetails.put("test2", Arrays.asList(2, 3, 4));
        final CatalogueResponse expectedCatalogueResponse =
            new CatalogueResponse(CatalogueResponseCode.CALLBACK_FAILURE, expectedDetails);
        final ApiException testException = new ApiException(expectedCatalogueResponse);

        // ACT
        final HttpError error = new HttpError(testException, request);
        final CatalogueResponse actualCatalogueResponse = error.getCatalogueResponse();

        // ASSERT
        assertThat(actualCatalogueResponse, is(equalTo(expectedCatalogueResponse)));
    }

    @Test
    public void shouldExtractMessageFromException() {
        final HttpError error = new HttpError(new IllegalArgumentException(MESSAGE), request);

        assertThat(error.getMessage(), is(equalTo(MESSAGE)));
    }

    @Test
    public void shouldExtractPathFromRequest() {
        final HttpError error = new HttpError(new IllegalArgumentException(MESSAGE), request);

        assertThat(error.getPath(), is(equalTo(PATH)));
    }

    @Test
    public void shouldTakeOptionalDetails() {
        final HttpError<String> error = new HttpError<String>(new IllegalArgumentException(MESSAGE), request)
            .withDetails(DETAILS);

        assertThat(error.getDetails(), is(equalTo(DETAILS)));
    }

    @Test
    public void shouldTakeOptionalCallbackErrors() {
        final HttpError error = new HttpError(new IllegalArgumentException(MESSAGE), request)
            .withCallbackErrors(CALLBACK_ERRORS);

        assertThat(error.getCallbackErrors(), is(equalTo(CALLBACK_ERRORS)));
    }

    @Test
    public void shouldTakeOptionalCallbackWarnings() {
        final HttpError error = new HttpError(new IllegalArgumentException(MESSAGE), request)
            .withCallbackWarnings(CALLBACK_WARNINGS);

        assertThat(error.getCallbackWarnings(), is(equalTo(CALLBACK_WARNINGS)));
    }

    @Test
    public void shouldExtractMessageFromExceptionAndStatus() {

        final Map<String, Object> expectedDetails = new HashMap<>();
        expectedDetails.put("test1", 1);
        expectedDetails.put("test2", Arrays.asList(2, 3, 4));

        final CatalogueResponse expectedCatalogueResponse =
            new CatalogueResponse(CatalogueResponseCode.CALLBACK_FAILURE, expectedDetails);

        final HttpError error = new HttpError(new IllegalArgumentException(MESSAGE), request, expectedCatalogueResponse, 400);

        final CatalogueResponse actualCatalogueResponse = error.getCatalogueResponse();
        assertThat(actualCatalogueResponse, is(equalTo(expectedCatalogueResponse)));
        assertThat(error.getStatus(), is(equalTo(400)));
    }

    @Test
    public void shouldExtractMessageFromExceptionWithoutStatus() {

        final Map<String, Object> expectedDetails = new HashMap<>();
        expectedDetails.put("test1", 1);
        expectedDetails.put("test2", Arrays.asList(2, 3, 4));

        final CatalogueResponse expectedCatalogueResponse =
            new CatalogueResponse(CatalogueResponseCode.CALLBACK_FAILURE, expectedDetails);

        final HttpError error = new HttpError(new IllegalArgumentException(MESSAGE), request, expectedCatalogueResponse, null);

        final CatalogueResponse actualCatalogueResponse = error.getCatalogueResponse();
        assertThat(actualCatalogueResponse, is(equalTo(expectedCatalogueResponse)));
        assertThat(error.getStatus(), is(equalTo(500)));
    }

    @ResponseStatus()
    class TestBlankResponseStatusException extends RuntimeException {}

    @ResponseStatus(
        code = HttpStatus.INTERNAL_SERVER_ERROR,
        value = HttpStatus.INTERNAL_SERVER_ERROR
    )
    class Test500StatusException extends RuntimeException {}

    @ResponseStatus(code = HttpStatus.UNSUPPORTED_MEDIA_TYPE)
    class TestCodeStatusException extends RuntimeException {}

    @ResponseStatus(value = HttpStatus.NOT_FOUND)
    class TestValueStatusException extends RuntimeException {}

    @ResponseStatus(reason = "Some error reason")
    class TestReasonException extends RuntimeException {}

}
