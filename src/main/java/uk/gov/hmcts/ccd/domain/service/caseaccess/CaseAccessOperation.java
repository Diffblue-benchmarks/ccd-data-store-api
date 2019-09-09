package uk.gov.hmcts.ccd.domain.service.caseaccess;

import org.elasticsearch.common.util.set.Sets;
import org.springframework.beans.factory.annotation.Qualifier;
import org.springframework.stereotype.Service;
import uk.gov.hmcts.ccd.data.caseaccess.CachedCaseRoleRepository;
import uk.gov.hmcts.ccd.data.caseaccess.CaseRoleRepository;
import uk.gov.hmcts.ccd.data.caseaccess.CaseUserRepository;
import uk.gov.hmcts.ccd.data.caseaccess.GlobalCaseRole;
import uk.gov.hmcts.ccd.data.caseaccess.SwitchableCaseUserRepository;
import uk.gov.hmcts.ccd.data.casedetails.CachedCaseDetailsRepository;
import uk.gov.hmcts.ccd.data.casedetails.CaseDetailsRepository;
import uk.gov.hmcts.ccd.domain.model.definition.CaseDetails;
import uk.gov.hmcts.ccd.domain.service.getcase.CaseNotFoundException;
import uk.gov.hmcts.ccd.endpoint.exceptions.InvalidCaseRoleException;
import uk.gov.hmcts.ccd.v2.external.domain.CaseUser;

import javax.transaction.Transactional;
import java.util.List;
import java.util.Optional;
import java.util.Set;
import java.util.stream.Collectors;

import static uk.gov.hmcts.ccd.data.caseaccess.GlobalCaseRole.CREATOR;

@Service
public class CaseAccessOperation {

    private final CaseUserRepository caseUserRepository;
    private final CaseDetailsRepository caseDetailsRepository;
    private final CaseRoleRepository caseRoleRepository;

    public CaseAccessOperation(@Qualifier(SwitchableCaseUserRepository.QUALIFIER) final CaseUserRepository caseUserRepository,
                               @Qualifier(CachedCaseDetailsRepository.QUALIFIER) final CaseDetailsRepository caseDetailsRepository,
                               @Qualifier(CachedCaseRoleRepository.QUALIFIER) CaseRoleRepository caseRoleRepository) {
        this.caseUserRepository = caseUserRepository;
        this.caseDetailsRepository = caseDetailsRepository;
        this.caseRoleRepository = caseRoleRepository;
    }

    @Transactional
    public void grantAccess(final String jurisdictionId, final String caseReference, final String userId) {
        final Optional<CaseDetails> maybeCase = caseDetailsRepository.findByReference(jurisdictionId,
            Long.valueOf(caseReference));

        final CaseDetails caseDetails = maybeCase.orElseThrow(() -> new CaseNotFoundException(caseReference));
        caseUserRepository.grantAccess(caseDetails.getCaseTypeId(), Long.valueOf(caseDetails.getId()), userId, CREATOR.getRole());
    }

    @Transactional
    public void revokeAccess(final String jurisdictionId, final String caseReference, final String userId) {
        final Optional<CaseDetails> maybeCase = caseDetailsRepository.findByReference(jurisdictionId,
            Long.valueOf(caseReference));
        final CaseDetails caseDetails = maybeCase.orElseThrow(() -> new CaseNotFoundException(caseReference));
        caseUserRepository.revokeAccess(caseDetails.getCaseTypeId(), Long.valueOf(caseDetails.getId()), userId, CREATOR.getRole());
    }

    public List<String> findCasesUserIdHasAccessTo(final String userId) {
        return caseUserRepository.findCasesUserIdHasAccessTo(userId)
            .stream()
            .map(databaseId -> caseDetailsRepository.findById(databaseId).getReference() + "")
            .collect(Collectors.toList());
    }

    @Transactional
    public void updateUserAccess(CaseDetails caseDetails, CaseUser caseUser) {
        final Set<String> validCaseRoles = caseRoleRepository.getCaseRoles(caseDetails.getCaseTypeId());
        final Set<String> globalCaseRoles = GlobalCaseRole.all();
        final Set<String> targetCaseRoles = caseUser.getCaseRoles();

        validateCaseRoles(Sets.union(globalCaseRoles, validCaseRoles), targetCaseRoles);

        final Long caseId = new Long(caseDetails.getId());
        final String userId = caseUser.getUserId();
        final List<String> currentCaseRoles = caseUserRepository.findCaseRoles(caseDetails.getCaseTypeId(), caseId, userId);

        grantAddedCaseRoles(caseDetails.getCaseTypeId(), userId, caseId, currentCaseRoles, targetCaseRoles);
        revokeRemovedCaseRoles(caseDetails.getCaseTypeId(), userId, caseId, currentCaseRoles, targetCaseRoles);
    }

    private void validateCaseRoles(Set<String> validCaseRoles, Set<String> targetCaseRoles) {
        targetCaseRoles.stream()
            .filter(role -> !validCaseRoles.contains(role))
            .findFirst()
            .ifPresent(role -> {
                throw new InvalidCaseRoleException(role);
            });
    }

    private void grantAddedCaseRoles(final String caseTypeId,
                                     final String userId,
                                     final Long caseId,
                                     final List<String> currentCaseRoles,
                                     final Set<String> targetCaseRoles) {
        targetCaseRoles.stream()
            .filter(targetRole -> !currentCaseRoles.contains(targetRole))
            .forEach(targetRole -> caseUserRepository.grantAccess(caseTypeId, caseId, userId, targetRole));
    }

    private void revokeRemovedCaseRoles(final String caseTypeId,
                                        final String userId,
                                        final Long caseId,
                                        final List<String> currentCaseRoles,
                                        final Set<String> targetCaseRoles) {
        currentCaseRoles.stream()
            .filter(currentRole -> !targetCaseRoles.contains(currentRole))
            .forEach(currentRole -> caseUserRepository.revokeAccess(caseTypeId, caseId, userId, currentRole));
    }
}
