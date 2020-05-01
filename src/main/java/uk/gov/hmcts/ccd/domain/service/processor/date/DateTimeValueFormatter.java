package uk.gov.hmcts.ccd.domain.service.processor.date;

import com.fasterxml.jackson.databind.JsonNode;
import com.fasterxml.jackson.databind.node.ArrayNode;
import com.fasterxml.jackson.databind.node.ObjectNode;
import com.fasterxml.jackson.databind.node.TextNode;
import org.springframework.beans.factory.annotation.Autowired;
import org.springframework.stereotype.Component;
import uk.gov.hmcts.ccd.domain.model.aggregated.CaseViewField;
import uk.gov.hmcts.ccd.domain.model.aggregated.CaseViewFieldBuilder;
import uk.gov.hmcts.ccd.domain.model.aggregated.CommonField;
import uk.gov.hmcts.ccd.domain.model.common.CommonDCPModel;
import uk.gov.hmcts.ccd.domain.model.common.DisplayContextParameter;
import uk.gov.hmcts.ccd.domain.model.common.DisplayContextParameterType;
import uk.gov.hmcts.ccd.domain.model.definition.DisplayContext;
import uk.gov.hmcts.ccd.domain.model.definition.WizardPageComplexFieldOverride;
import uk.gov.hmcts.ccd.domain.service.processor.CaseViewFieldProcessor;
import uk.gov.hmcts.ccd.domain.types.BaseType;

import java.util.*;

import static uk.gov.hmcts.ccd.domain.model.common.DisplayContextParameterType.DATETIMEDISPLAY;
import static uk.gov.hmcts.ccd.domain.model.common.DisplayContextParameterType.DATETIMEENTRY;
import static uk.gov.hmcts.ccd.domain.model.definition.FieldTypeDefinition.*;
import static uk.gov.hmcts.ccd.domain.service.processor.date.DateTimeFormatParser.DATE_FORMAT;
import static uk.gov.hmcts.ccd.domain.service.processor.date.DateTimeFormatParser.DATE_TIME_FORMAT;
import static uk.gov.hmcts.ccd.domain.types.CollectionValidator.VALUE;

@Component
public class DateTimeValueFormatter extends CaseViewFieldProcessor {

    private static final List<String> SUPPORTED_TYPES = Arrays.asList(DATETIME, DATE);
    private static final Map<DisplayContext, DisplayContextParameterType> ENUM_MAP = new EnumMap<>(DisplayContext.class);

    private final DateTimeFormatParser dateTimeFormatParser;

    static {
        ENUM_MAP.put(DisplayContext.MANDATORY, DATETIMEENTRY);
        ENUM_MAP.put(DisplayContext.OPTIONAL, DATETIMEENTRY);
        ENUM_MAP.put(DisplayContext.READONLY, DATETIMEDISPLAY);
    }

    @Autowired
    public DateTimeValueFormatter(CaseViewFieldBuilder caseViewFieldBuilder,
                                  DateTimeFormatParser dateTimeFormatParser) {
        super(caseViewFieldBuilder);
        this.dateTimeFormatParser = dateTimeFormatParser;
    }

    @Override
    protected CaseViewField executeSimple(CaseViewField caseViewField, BaseType baseType) {
        caseViewField.setFormattedValue(
            caseViewField.getValue() instanceof TextNode
                ? executeSimple((TextNode) caseViewField.getValue(), caseViewField, baseType, caseViewField.getId(), null, caseViewField)
                : caseViewField.getValue()
        );

        return caseViewField;
    }

    @Override
    protected JsonNode executeSimple(JsonNode node,
                                     CommonField field,
                                     BaseType baseType,
                                     String fieldPath,
                                     WizardPageComplexFieldOverride override,
                                     CommonField topLevelField) {
        final DisplayContext displayContext = displayContext(topLevelField, override);
        return !isNullOrEmpty(node)
            && field.hasDisplayContextParameter(ENUM_MAP.get(displayContext))
            && isSupportedBaseType(baseType, SUPPORTED_TYPES)
                ? createNode(field, node.asText(), baseType, fieldPath, displayContext)
                : node;
    }

    @Override
    protected CaseViewField executeCollection(CaseViewField caseViewField) {
        caseViewField.setFormattedValue(
            caseViewField.getValue() instanceof ArrayNode
                ? executeCollection((ArrayNode) caseViewField.getValue(), caseViewField, caseViewField.getId(), null, caseViewField)
                : caseViewField.getValue()
        );

        return caseViewField;
    }

    protected JsonNode executeCollection(JsonNode collectionNode,
                                         CommonField field,
                                         String fieldPath,
                                         WizardPageComplexFieldOverride override,
                                         CommonField topLevelField) {
        final BaseType collectionFieldType = BaseType.get(field.getFieldTypeDefinition().getCollectionFieldTypeDefinition().getType());
        final DisplayContext displayContext = displayContext(topLevelField, override);

        if ((field.hasDisplayContextParameter(ENUM_MAP.get(displayContext))
            && isSupportedBaseType(collectionFieldType, SUPPORTED_TYPES))
            || BaseType.get(COMPLEX) == collectionFieldType) {
            ArrayNode newNode = MAPPER.createArrayNode();
            collectionNode.forEach(item -> {
                JsonNode newItem = item.deepCopy();
                ((ObjectNode)newItem).replace(VALUE,
                    isSupportedBaseType(collectionFieldType, SUPPORTED_TYPES)
                        ? createNode(
                            field,
                            item.get(VALUE).asText(),
                            collectionFieldType,
                            fieldPath,
                            displayContext)
                        : executeComplex(
                            item.get(VALUE),
                            field.getFieldTypeDefinition().getChildren(),
                            null,
                            fieldPath,
                            topLevelField));
                newNode.add(newItem);
            });

            return newNode;
        }

        return collectionNode;
    }

    private TextNode createNode(CommonDCPModel field, String valueToConvert, BaseType baseType, String fieldPath, DisplayContext displayContext) {
        if (ENUM_MAP.containsKey(displayContext)) {
            String format = format(field, displayContext, baseType);
            return dateTimeFormatParser.valueToTextNode(valueToConvert, baseType, fieldPath, format, false);
        }

        return new TextNode(valueToConvert);
    }

    private String format(CommonDCPModel field, DisplayContext displayContext, BaseType baseType) {
        return field.getDisplayContextParameter(ENUM_MAP.get(displayContext))
            .map(DisplayContextParameter::getValue)
            .orElseGet(() -> baseType == BaseType.get(DATETIME) ? DATE_TIME_FORMAT : DATE_FORMAT);
    }
}
